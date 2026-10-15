import Lean
import Jsp000404.K3bGeometryPart7
import Jsp000404.K3bGeometry
import Jsp000404.OneSaturatedHigh
open Lean Elab Command
elab "#localaudit " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "module missing"
  let names := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc n _ =>
    if env.getModuleIdxFor? n == some idx && !n.isInternalDetail then acc.push n else acc
  logInfo m!"AUDITMOD {m.getId} {names.size}"
  for n in names do
    let ax ← collectAxioms n
    logInfo m!"AUDITDECL {m.getId} {n} AXIOMS {ax.toList}"
#localaudit Jsp000404.K3bGeometryPart7
#localaudit Jsp000404.K3bGeometry
#localaudit Jsp000404.OneSaturatedHigh
