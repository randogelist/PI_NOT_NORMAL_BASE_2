#!/usr/bin/env python3
"""Check that the audit accepts an honest theorem and rejects hidden proof assumptions."""
import argparse
from types import SimpleNamespace
import shutil
import json
import os
from pathlib import Path
import subprocess
import tempfile
import verify

parser = argparse.ArgumentParser()
parser.add_argument('--lean', default='lean')
args = parser.parse_args()
verify.require_target_ci()
template = (Path(__file__).parent / 'audit_template.lean').read_text()
results = []
with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    for name, code, expected in [
        ('Good', 'theorem honest : True := True.intro\n', True),
        ('Bad', 'axiom hiddenBad : False\ntheorem downstreamBad : False := hiddenBad\n', False),
        ('Hole', 'theorem incomplete : False := by sorry\n', False),
    ]:
        source = root / f'{name}.lean'
        source.write_text(code)
        compile_result = subprocess.run([args.lean, '-o', str(root / f'{name}.olean'), str(source)], cwd=root, text=True, capture_output=True)
        if compile_result.returncode: raise RuntimeError(compile_result.stdout + compile_result.stderr)
        audit = root / ('Audit' + name + '.lean')
        audit.write_text(f'import {name}\n' + template.replace('__MODULES__', '#[`' + name + ']'))
        env = dict(os.environ, LEAN_PATH=str(root))
        result = subprocess.run([args.lean, str(audit)], cwd=root, env=env, text=True, capture_output=True)
        passed = result.returncode == 0 and 'AXIOM_AUDIT_JSON:' in result.stdout
        if passed != expected: raise RuntimeError(f'{name}: unexpected audit result\n{result.stdout}\n{result.stderr}')
        if not expected and 'FORBIDDEN_AXIOMS' not in result.stdout: raise RuntimeError(f'{name}: failed for wrong reason')
        try:
            verify.check_source(source)
            lint = True
        except ValueError:
            lint = False
        if lint != expected: raise RuntimeError(f'{name}: source guard failed')
        results.append({'fixture': name, 'accepted': passed, 'expected': expected, 'status': 'PASS'})
    nested = root / 'Comments.lean'
    nested.write_text('/- outer /- sorry -/ axiom -/\n-- unsafe\ndef commentString : String := "sorry axiom"\n')
    verify.check_source(nested)
# Reject unsupported multi-import syntax instead of silently omitting dependencies.
with tempfile.TemporaryDirectory() as tmp:
    path = Path(tmp) / "Imports.lean"
    path.write_text("public meta import all First.Second\nimport Third\n")
    if verify.check_source(path) != ["First.Second", "Third"]: raise RuntimeError("Import modifier parsing failed")
    path.write_text("import First Second\n")
    try:
        verify.check_source(path)
        raise RuntimeError("Multi-import syntax was silently accepted")
    except ValueError:
        pass
    results.append({"fixture":"import_parser","status":"PASS"})
# A removed source must not survive through an old project .olean on LEAN_PATH.
name = "verifier-stale-test"
try:
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        (directory / "Top.lean").write_text("import Removed\ntheorem fresh : True := True.intro\n")
        stale = verify.ROOT / ".verify/build" / name / "Removed.olean"
        stale.parent.mkdir(parents=True, exist_ok=True)
        stale.write_bytes(b"stale project artifact")
        config = SimpleNamespace(lean="MUST_NOT_BE_CALLED", audit_existing=False)
        try:
            verify.verify_project(name, directory, verify.modules_at(directory), config, [], {})
            raise RuntimeError("Deleted module was accepted from stale artifacts")
        except RuntimeError as error:
            if "Import absent from explicit" not in str(error): raise
        if stale.exists(): raise RuntimeError("Stale project artifact was retained")
        results.append({"fixture":"deleted_module_rejection","status":"PASS"})
finally:
    shutil.rmtree(verify.ROOT / '.verify/build' / name, ignore_errors=True)
    shutil.rmtree(verify.ROOT / 'verification' / name, ignore_errors=True)
# Exercise cache invalidation on a two-module dependency chain.
name = "verifier-cache-test"
try:
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        (directory / "Base.lean").write_text("theorem base_value : 1 = 1 := rfl\n")
        (directory / "Top.lean").write_text("import Base\ntheorem derived_value : 1 = 1 := base_value\n")
        modules = verify.modules_at(directory)
        config = SimpleNamespace(lean=args.lean, audit_existing=False)
        paths = [Path(subprocess.check_output([args.lean, '--print-libdir'], text=True).strip())]
        environment = {"external_fingerprint": "builtin-test-environment", "lean_version": subprocess.check_output([args.lean, '--version'], text=True).strip()}
        first = verify.verify_project(name, directory, modules, config, paths, environment)
        second = verify.verify_project(name, directory, modules, config, paths, environment)
        if set(first['compiled']) != {'Base', 'Top'} or set(second['frozen_reused']) != {'Base', 'Top'}:
            raise RuntimeError('Expected first compile followed by frozen reuse')
        (directory / "Base.lean").write_text("-- changed source\ntheorem base_value : 1 = 1 := rfl\n")
        changed = verify.verify_project(name, directory, modules, config, paths, environment)
        if set(changed['compiled']) != {'Base', 'Top'}: raise RuntimeError('Dependency change did not invalidate downstream module')
        target = verify.ROOT / '.verify/build' / name / 'Base.olean'
        target.write_bytes(b'corrupt artifact')
        tampered = verify.verify_project(name, directory, modules, config, paths, environment)
        if 'Base' not in tampered['compiled']: raise RuntimeError('Corrupt cached output was reused')
        results.append({'fixture':'cache_invalidation','status':'PASS','checks':['first_compile','frozen_reuse','source_and_dependency_change','tampered_output']})
finally:
    shutil.rmtree(verify.ROOT / '.verify/build' / name, ignore_errors=True)
    shutil.rmtree(verify.ROOT / 'verification' / name, ignore_errors=True)
    (verify.ROOT / '.verify/receipts' / (name + '.json')).unlink(missing_ok=True)
print(json.dumps({'status':'PASS', 'tests':results, 'nested_comments_and_strings':'PASS'}, indent=2))
