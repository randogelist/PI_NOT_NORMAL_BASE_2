#!/usr/bin/env python3
"""CI-only compilation and axiom audit for randogelist/PI_NOT_NORMAL_BASE_2.

A PASS certifies exact conditional theorem statements, never their hypotheses.
Cached outputs are reusable only with matching source/dependency/toolchain fingerprints
and matching output bytes. The axiom scan is always rerun.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
MATHLIB_REV = "db584cd6d46c92f209a44c0f1c829460d327499d"
LEAN_COMMIT = "d8b18978322de05a8f3dba51ef03cf5461676c17"
ALLOWLIST = ["propext", "Classical.choice", "Quot.sound"]
TARGET_REPOSITORY = "randogelist/PI_NOT_NORMAL_BASE_2"
FLAGS = ["-j1", "-DmaxRecDepth=4096", "-DmaxHeartbeats=0"]


def require_target_ci() -> None:
    if os.environ.get("GITHUB_ACTIONS") != "true" or os.environ.get("GITHUB_REPOSITORY") != TARGET_REPOSITORY:
        raise RuntimeError("CI_ONLY: Lean execution is authorized only on GitHub Actions for " + TARGET_REPOSITORY)


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(data)
    return h.hexdigest()


def object_digest(obj) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode()).hexdigest()


def strip_comments_and_strings(text: str) -> str:
    # Lean nested block comments, line comments, and string literals.
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        ch, pair = text[i], text[i:i + 2]
        if depth:
            if pair == "/-": depth += 1; i += 2
            elif pair == "-/": depth -= 1; i += 2
            else: out.append("\n" if ch == "\n" else " "); i += 1
        elif quoted:
            if ch == "\\": out.extend("  "); i += 2
            elif ch == '"': quoted = False; out.append(" "); i += 1
            else: out.append("\n" if ch == "\n" else " "); i += 1
        elif pair == "/-": depth = 1; out.extend("  "); i += 2
        elif pair == "--":
            j = text.find("\n", i)
            if j < 0: j = len(text)
            out.extend(" " * (j - i)); i = j
        elif ch == '"': quoted = True; out.append(" "); i += 1
        else: out.append(ch); i += 1
    if depth or quoted: raise ValueError("Unterminated comment or string")
    return "".join(out)


def check_source(path: Path) -> list[str]:
    code = strip_comments_and_strings(path.read_text(encoding="utf-8-sig"))
    forbidden = r"\b(?:sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|run_cmd|elab|macro|initialize|builtin_initialize)\b|debug\.skipKernelTC"
    match = re.search(forbidden, code)
    if match:
        raise ValueError(f"Forbidden proof-source token {match.group()!r} in {path}")
    imports = []
    for line in code.splitlines():
        if not re.search(r"\bimport\b", line): continue
        match = re.fullmatch(r"[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?([A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)[ \t]*", line)
        if not match:
            raise ValueError(f"Unsupported/multiple import syntax in {path}: {line.strip()}")
        imports.append(match.group(1))
    return imports


def modules_at(directory: Path, primary=False) -> dict[str, Path]:
    # Primary proof sources live outside isolated branches, provenance and tooling.
    # Discover all such modules so a newly added root theorem cannot escape CI.
    excluded = {"verification", "scripts", "provenance", "branches"} if primary else {"verification"}
    modules = {}
    for p in sorted(directory.rglob("*.lean")):
        relative = p.relative_to(directory)
        if any(part.startswith(".") or part in excluded for part in relative.parts): continue
        if relative.name == "lakefile.lean": continue
        modules[".".join(relative.with_suffix("").parts)] = p
    return modules


def topological(modules, imports):
    done, active, order = set(), set(), []
    def visit(name):
        if name in done: return
        if name in active: raise ValueError(f"Import cycle at {name}")
        active.add(name)
        for dep in imports[name]:
            if dep in modules: visit(dep)
        active.remove(name); done.add(name); order.append(name)
    for name in modules: visit(name)
    return order


def execute(command, cwd, env, log):
    require_target_ci()
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(result.stdout, encoding="utf-8")
    if result.returncode:
        print(result.stdout[-10000:], file=sys.stderr)
        raise RuntimeError(f"Command failed ({result.returncode}); see {log.relative_to(ROOT)}")
    return result.stdout


def artifact_hashes(olean: Path):
    return {p.name: digest(p) for p in sorted(olean.parent.glob(olean.name + "*"))
            if p.is_file() and not p.name.endswith((".hash", ".sig"))}


def verify_project(name, directory, modules, args, external_paths, environment):
    require_target_ci()
    imports = {module: check_source(path) for module, path in modules.items()}
    order = topological(modules, imports)
    logs = ROOT / "verification" / name
    logs.mkdir(parents=True, exist_ok=True)
    build = (directory / ".lake/build/lib/lean" if name == "primary" else directory / ".build") if args.audit_existing else ROOT / ".verify/build" / name
    build.mkdir(parents=True, exist_ok=True)
    # Never let a deleted/renamed project module survive as an unaudited import.
    for stale in build.rglob("*.olean*"):
        base = str(stale.relative_to(build)).split(".olean", 1)[0]
        module = ".".join(Path(base).parts)
        if module not in modules:
            if args.audit_existing:
                raise RuntimeError(f"Unexpected stale project artifact: {stale}")
            stale.unlink()
    for imported in {dep for deps in imports.values() for dep in deps if dep not in modules}:
        relative = Path(*imported.split(".")).with_suffix(".olean")
        if not any((external / relative).is_file() for external in external_paths):
            raise RuntimeError(f"Import absent from explicit project/dependency inventories: {name}:{imported}")
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(str(p) for p in [build, *external_paths]))
    cache_path = ROOT / ".verify/receipts" / (name + ".json")
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    entries, rebuilt, reused = {}, [], []
    external_receipt = None
    external_entries = {}
    if args.audit_existing:
        evidence = (ROOT / "verification/primary/BUILD_RECEIPT.json") if name == "primary" else directory / "verification/BUILD_RECEIPT.json"
        if not evidence.is_file(): raise RuntimeError(f"Missing compiler evidence: {evidence}")
        external_receipt = json.loads(evidence.read_text())
        if external_receipt.get("status") != "PASS": raise RuntimeError(f"Compiler receipt is not PASS: {evidence}")
        recorded_env = external_receipt.get("environment", {})
        if recorded_env.get("lean_version") != environment["lean_version"] or recorded_env.get("mathlib_commit") != environment["mathlib_commit"]:
            raise RuntimeError(f"Compiler receipt environment differs: {evidence}")
        external_entries = {item["module"]: item for item in external_receipt["modules"]}
        if set(external_entries) != set(modules): raise RuntimeError(f"Compiler receipt module coverage differs: {evidence}")
    for module in order:
        path = modules[module]
        target = build.joinpath(*module.split(".")).with_suffix(".olean")
        key = object_digest({"source": digest(path), "environment": environment,
                             "imports": {dep: {"key": entries[dep]["key"], "outputs": entries[dep]["outputs"]} if dep in modules else environment["external_fingerprint"] for dep in imports[module]}})
        previous = cache.get(module, {})
        current_output = artifact_hashes(target) if target.exists() else {}
        if args.audit_existing:
            if not target.exists(): raise RuntimeError(f"Missing existing build {target}")
            record = external_entries[module]
            if record.get("status") != "PASS" or record.get("return_code") != 0 or record.get("source_sha256") != digest(path):
                raise RuntimeError(f"Unverified source/compiler result for {name}:{module}")
            expected_imports = {dep: entries[dep]["outputs"] for dep in imports[module] if dep in modules}
            if record.get("local_import_artifacts", {}) != expected_imports:
                raise RuntimeError(f"Compile-time dependency artifacts differ: {name}:{module}")
            command = record.get("command", [])
            if "skipKernelTC" in str(command) or "--trust" in str(command):
                raise RuntimeError(f"Unsupported compiler trust override: {name}:{module}")
            recorded_artifacts = {Path(p).name: sha for p, sha in record["artifacts"].items() if not p.endswith((".hash", ".sig"))}
            if recorded_artifacts != current_output: raise RuntimeError(f"Compiler artifact fingerprint differs: {name}:{module}")
            mode = "EXTERNAL_BUILD_AUDITED"
        elif (previous.get("key") == key and current_output and previous.get("outputs") == current_output):
            mode = "FROZEN_REUSE"; reused.append(module)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            execute([args.lean, *FLAGS, "-o", str(target), str(path)], directory, env, logs / (module + ".log"))
            mode = "COMPILED"; rebuilt.append(module)
        entries[module] = {"key": key, "source_sha256": digest(path), "outputs": artifact_hashes(target), "mode": mode}
        print(f"{name}:{module}:{mode}", flush=True)
    template = (ROOT / "scripts/audit_template.lean").read_text()
    names = "#[" + ", ".join("`" + module for module in order) + "]"
    audit_source = "".join("import " + module + "\n" for module in order) + template.replace("__MODULES__", names)
    audit_path = logs / "AllDeclarationsAudit.lean"
    audit_path.write_text(audit_source)
    output = execute([args.lean, *FLAGS, str(audit_path)], ROOT, env, logs / "axioms.log")
    rows = [line.split("AXIOM_AUDIT_JSON:", 1)[1] for line in output.splitlines() if "AXIOM_AUDIT_JSON:" in line]
    if len(rows) != 1: raise RuntimeError(f"Missing or duplicated complete axiom audit for {name}")
    audit = json.loads(rows[0])
    if audit.get("status") != "PASS" or not audit.get("declarations"): raise RuntimeError(f"Empty/failed audit for {name}")
    (logs / "axioms.json").write_text(json.dumps(audit, indent=2) + "\n")
    if not args.audit_existing:
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        cache_path.write_text(json.dumps(entries, indent=2) + "\n")
    return {"status": "PASS", "compile_mode": "EXTERNAL_BUILD_AUDITED" if args.audit_existing else "COMPILED_OR_FINGERPRINT_REUSED",
            "module_count": len(order), "declaration_count": len(audit["declarations"]),
            "compiled": rebuilt, "frozen_reused": reused, "modules": entries,
            "axiom_union": sorted({ax for row in audit["declarations"] for ax in row["axioms"]}),
            "external_compiler_receipt_sha256": digest(evidence) if external_receipt else None}


def main():
    require_target_ci()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, default=ROOT / ".lake/packages/mathlib")
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--project", action="append", help="primary or isolated branch name; default all")
    args = parser.parse_args()
    args.audit_existing = False  # Only hosted compilation / verified hosted cache reuse is permitted.
    args.mathlib = args.mathlib.resolve()
    args.lean = shutil.which(args.lean) or args.lean
    receipt = {"status": "FAIL", "created_unix": int(time.time()), "pi_not_normal_unconditional": False,
               "allowed_axioms": ALLOWLIST, "projects": {},
               "execution_location": "GITHUB_ACTIONS_ONLY", "repository": TARGET_REPOSITORY,
               "github_sha": os.environ.get("GITHUB_SHA"), "github_run_id": os.environ.get("GITHUB_RUN_ID")}
    dest = ROOT / "verification/receipt.json"
    dest.parent.mkdir(parents=True, exist_ok=True)
    try:
        version = subprocess.check_output([args.lean, "--version"], text=True).strip()
        if "version 4.33.0," not in version or LEAN_COMMIT not in version: raise RuntimeError(f"Wrong Lean: {version}")
        rev = subprocess.check_output(["git", "-C", str(args.mathlib), "rev-parse", "HEAD"], text=True).strip()
        if rev != MATHLIB_REV: raise RuntimeError(f"Wrong Mathlib commit {rev}")
        paths = [args.mathlib / ".lake/build/lib/lean"]
        # Lake places dependencies beside mathlib in a user project, but inside it in a standalone cache.
        for base in [args.mathlib / ".lake/packages", ROOT / ".lake/packages"]:
            if base.exists():
                for p in sorted(base.iterdir()):
                    lib = p.resolve() / ".lake/build/lib/lean"
                    if lib.is_dir() and lib not in paths: paths.append(lib)
        libdir = Path(subprocess.check_output([args.lean, "--print-libdir"], text=True).strip())
        paths.append(libdir)
        # Hash the full imported cache, including private kernel data and tactic runtime. This detects dependency
        # changes even when a cache directory retains the same git commit and timestamps.
        fingerprint = hashlib.sha256()
        for index, base in enumerate(paths):
            for p in sorted(base.rglob("*")):
                if not p.is_file() or p.name.endswith((".hash", ".sig")): continue
                if not (".olean" in p.name or p.suffix in {".ir", ".so", ".dll", ".dylib"}): continue
                fingerprint.update(f"{index}/{p.relative_to(base)}\0{digest(p)}\n".encode())
        environment = {"lean_version": version, "lean_executable_sha256": digest(Path(args.lean)),
                       "mathlib_commit": rev, "external_fingerprint": fingerprint.hexdigest(), "flags": FLAGS,
                       "lean_native_executable_sha256": digest(libdir.parent.parent / "bin/lean"),
                       "platform": sys.platform, "verifier_sha256": digest(Path(__file__)), "audit_template_sha256": digest(ROOT / "scripts/audit_template.lean")}
        receipt["environment"] = environment
        projects = [("primary", ROOT, modules_at(ROOT, primary=True))]
        for directory in sorted((ROOT / "branches").iterdir()):
            if directory.is_dir() and not directory.name.startswith("."):
                modules = modules_at(directory)
                if modules: projects.append((directory.name, directory, modules))
        if args.project:
            unknown = set(args.project) - {p[0] for p in projects}
            if unknown: raise RuntimeError(f"Unknown projects: {unknown}")
            projects = [p for p in projects if p[0] in args.project]
        for name, directory, modules in projects:
            receipt["projects"][name] = verify_project(name, directory, modules, args, paths, environment)
            dest.write_text(json.dumps(receipt, indent=2) + "\n")
        receipt["status"] = "PASS"
    except Exception as exc:
        receipt["error"] = str(exc)
        print(f"VERIFICATION_FAIL: {exc}", file=sys.stderr)
    finally:
        dest.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"VERIFICATION_{receipt['status']}: {dest}")
    return 0 if receipt["status"] == "PASS" else 1

if __name__ == "__main__":
    raise SystemExit(main())
