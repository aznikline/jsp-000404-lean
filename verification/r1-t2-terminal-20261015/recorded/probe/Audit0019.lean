import Lean
import Jsp000404.ProjectionDescentCore
import Jsp000404.ProjectionDescent
import Jsp000404.StarReceiver
import Jsp000404.MixedStarExclusion
import Jsp000404.S7N7Defs
import Jsp000404.S7N7Core
import Jsp000404.R1LeavesN7_11S0
import Jsp000404.R1LeavesN7_11S1
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
#localaudit Jsp000404.ProjectionDescentCore
#localaudit Jsp000404.ProjectionDescent
#localaudit Jsp000404.StarReceiver
#localaudit Jsp000404.MixedStarExclusion
#localaudit Jsp000404.S7N7Defs
#localaudit Jsp000404.S7N7Core
#localaudit Jsp000404.R1LeavesN7_11S0
#localaudit Jsp000404.R1LeavesN7_11S1
