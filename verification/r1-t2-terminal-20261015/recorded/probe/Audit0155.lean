import Lean
import Jsp000404.R1LeavesN7_5S30
import Jsp000404.R1LeavesN7_60S3
import Jsp000404.R1LeavesN7_60S4
import Jsp000404.R1LeavesN7_60S5
import Jsp000404.R1LeavesN7_60S6
import Jsp000404.R1LeavesN7_62S4
import Jsp000404.R1LeavesN7_62S5
import Jsp000404.R1LeavesN7_63S10
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
#localaudit Jsp000404.R1LeavesN7_5S30
#localaudit Jsp000404.R1LeavesN7_60S3
#localaudit Jsp000404.R1LeavesN7_60S4
#localaudit Jsp000404.R1LeavesN7_60S5
#localaudit Jsp000404.R1LeavesN7_60S6
#localaudit Jsp000404.R1LeavesN7_62S4
#localaudit Jsp000404.R1LeavesN7_62S5
#localaudit Jsp000404.R1LeavesN7_63S10
