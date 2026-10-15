import Lean
import Jsp000404.R1LeavesN7_40S14
import Jsp000404.R1LeavesN7_40S15
import Jsp000404.R1LeavesN7_43S9
import Jsp000404.R1LeavesN7_43S10
import Jsp000404.R1LeavesN7_43S11
import Jsp000404.R1LeavesN7_43S12
import Jsp000404.R1LeavesN7_47S0
import Jsp000404.R1LeavesN7_47S1
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
#localaudit Jsp000404.R1LeavesN7_40S14
#localaudit Jsp000404.R1LeavesN7_40S15
#localaudit Jsp000404.R1LeavesN7_43S9
#localaudit Jsp000404.R1LeavesN7_43S10
#localaudit Jsp000404.R1LeavesN7_43S11
#localaudit Jsp000404.R1LeavesN7_43S12
#localaudit Jsp000404.R1LeavesN7_47S0
#localaudit Jsp000404.R1LeavesN7_47S1
