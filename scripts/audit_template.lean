-- Generated module imports are prepended by verify.py.
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let projectModules : Array Name := __MODULES__
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut declarations := #[]
  let mut seenModules : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      if projectModules.contains moduleName then
        if !seenModules.contains moduleName then
          seenModules := seenModules.push moduleName
        let axioms ← collectAxioms name
        let forbidden := axioms.filter fun ax => !allowed.contains ax
        if !forbidden.isEmpty then
          throwError "FORBIDDEN_AXIOMS {name}: {forbidden}"
        let row := Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson moduleName.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        declarations := declarations.push row
  if declarations.isEmpty then
    throwError "EMPTY_PROJECT_AUDIT"
  let row := Json.mkObj [
    ("status", toJson "PASS"),
    ("declarations", toJson declarations),
    ("modules_with_declarations", toJson (seenModules.map Name.toString)),
    ("imported_project_modules", toJson (projectModules.map Name.toString))]
  logInfo m!"AXIOM_AUDIT_JSON:{row.compress}"
