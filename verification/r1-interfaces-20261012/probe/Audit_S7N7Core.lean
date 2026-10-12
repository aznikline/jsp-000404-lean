import Jsp000404.S7N7Core
open Lean Elab Command

elab "#audit_module " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "module not found"
  let all := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc n _ =>
    if env.getModuleIdxFor? n == some idx then acc.push n else acc
  let names := (all.filter (fun n => !n.isInternalDetail)).qsort (fun a b => a.toString < b.toString)
  logInfo m!"module {m.getId}: {all.size} constants, {names.size} non-internal"
  for n in names do
    let ci ← getConstInfo n
    let axs ← collectAxioms n
    logInfo m!"DECL {n} : {ci.type}\nAXIOMS {n}: {axs.toList}"

#audit_module Jsp000404.S7N7Core
