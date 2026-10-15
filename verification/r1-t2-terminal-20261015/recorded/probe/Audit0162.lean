import Lean
import Jsp000404.R1LeavesN7_14S15
import Jsp000404.R1LeavesN7_14S16
import Jsp000404.R1LeavesN7_14S17
import Jsp000404.R1LeavesN7_14S18
import Jsp000404.R1LeavesN7_14S19
import Jsp000404.R1LeavesN7_14S2
import Jsp000404.R1LeavesN7_14S3
import Jsp000404.R1LeavesN7_14S4
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
#localaudit Jsp000404.R1LeavesN7_14S15
#localaudit Jsp000404.R1LeavesN7_14S16
#localaudit Jsp000404.R1LeavesN7_14S17
#localaudit Jsp000404.R1LeavesN7_14S18
#localaudit Jsp000404.R1LeavesN7_14S19
#localaudit Jsp000404.R1LeavesN7_14S2
#localaudit Jsp000404.R1LeavesN7_14S3
#localaudit Jsp000404.R1LeavesN7_14S4
