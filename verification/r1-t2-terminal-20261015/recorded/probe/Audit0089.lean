import Lean
import Jsp000404.R1LeavesN7_37S2
import Jsp000404.R1LeavesN7_37S3
import Jsp000404.R1LeavesN7_37S4
import Jsp000404.R1LeavesN7_40S0
import Jsp000404.R1LeavesN7_40S1
import Jsp000404.R1LeavesN7_40S2
import Jsp000404.R1LeavesN7_40S3
import Jsp000404.R1LeavesN7_40S4
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
#localaudit Jsp000404.R1LeavesN7_37S2
#localaudit Jsp000404.R1LeavesN7_37S3
#localaudit Jsp000404.R1LeavesN7_37S4
#localaudit Jsp000404.R1LeavesN7_40S0
#localaudit Jsp000404.R1LeavesN7_40S1
#localaudit Jsp000404.R1LeavesN7_40S2
#localaudit Jsp000404.R1LeavesN7_40S3
#localaudit Jsp000404.R1LeavesN7_40S4
