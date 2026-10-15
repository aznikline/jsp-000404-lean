import Lean
import Jsp000404.TwoSaturatedFour
import Jsp000404.TriangleRestriction
import Jsp000404.ThreeDirectionCapacity
import Jsp000404.TwoSaturatedDeficit
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
#localaudit Jsp000404.TwoSaturatedFour
#localaudit Jsp000404.TriangleRestriction
#localaudit Jsp000404.ThreeDirectionCapacity
#localaudit Jsp000404.TwoSaturatedDeficit
