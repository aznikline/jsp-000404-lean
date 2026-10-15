import Lean
import Jsp000404.R1LeavesN7_9S2
import Jsp000404.R1LeavesN7_9S3
import Jsp000404.R1LeavesN7_9S4
import Jsp000404.R1LeavesN7_9S5
import Jsp000404.R1LeavesN7_9S6
import Jsp000404.R1LeavesN7_9S7
import Jsp000404.R1LeavesN7_9S8
import Jsp000404.R1LeavesN7_9S11
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
#localaudit Jsp000404.R1LeavesN7_9S2
#localaudit Jsp000404.R1LeavesN7_9S3
#localaudit Jsp000404.R1LeavesN7_9S4
#localaudit Jsp000404.R1LeavesN7_9S5
#localaudit Jsp000404.R1LeavesN7_9S6
#localaudit Jsp000404.R1LeavesN7_9S7
#localaudit Jsp000404.R1LeavesN7_9S8
#localaudit Jsp000404.R1LeavesN7_9S11
