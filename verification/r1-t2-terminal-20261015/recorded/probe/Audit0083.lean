import Lean
import Jsp000404.R1LeavesN7_0S86
import Jsp000404.R1LeavesN7_0S87
import Jsp000404.R1LeavesN7_0S88
import Jsp000404.R1LeavesN7_0S89
import Jsp000404.R1LeavesN7_0S90
import Jsp000404.R1LeavesN7_12S0
import Jsp000404.R1LeavesN7_12S1
import Jsp000404.R1LeavesN7_12S10
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
#localaudit Jsp000404.R1LeavesN7_0S86
#localaudit Jsp000404.R1LeavesN7_0S87
#localaudit Jsp000404.R1LeavesN7_0S88
#localaudit Jsp000404.R1LeavesN7_0S89
#localaudit Jsp000404.R1LeavesN7_0S90
#localaudit Jsp000404.R1LeavesN7_12S0
#localaudit Jsp000404.R1LeavesN7_12S1
#localaudit Jsp000404.R1LeavesN7_12S10
