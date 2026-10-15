import Lean
import Jsp000404.R1LeavesN7_3S40
import Jsp000404.R1LeavesN7_3S41
import Jsp000404.R1LeavesN7_3S42
import Jsp000404.R1LeavesN7_40S10
import Jsp000404.R1LeavesN7_40S5
import Jsp000404.R1LeavesN7_40S6
import Jsp000404.R1LeavesN7_40S7
import Jsp000404.R1LeavesN7_40S8
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
#localaudit Jsp000404.R1LeavesN7_3S40
#localaudit Jsp000404.R1LeavesN7_3S41
#localaudit Jsp000404.R1LeavesN7_3S42
#localaudit Jsp000404.R1LeavesN7_40S10
#localaudit Jsp000404.R1LeavesN7_40S5
#localaudit Jsp000404.R1LeavesN7_40S6
#localaudit Jsp000404.R1LeavesN7_40S7
#localaudit Jsp000404.R1LeavesN7_40S8
