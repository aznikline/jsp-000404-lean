import Lean
import Jsp000404.R1LeavesN7_1S56
import Jsp000404.R1LeavesN7_1S57
import Jsp000404.R1LeavesN7_21S0
import Jsp000404.R1LeavesN7_21S1
import Jsp000404.R1LeavesN7_21S2
import Jsp000404.R1LeavesN7_21S3
import Jsp000404.R1LeavesN7_21S4
import Jsp000404.R1LeavesN7_21S5
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
#localaudit Jsp000404.R1LeavesN7_1S56
#localaudit Jsp000404.R1LeavesN7_1S57
#localaudit Jsp000404.R1LeavesN7_21S0
#localaudit Jsp000404.R1LeavesN7_21S1
#localaudit Jsp000404.R1LeavesN7_21S2
#localaudit Jsp000404.R1LeavesN7_21S3
#localaudit Jsp000404.R1LeavesN7_21S4
#localaudit Jsp000404.R1LeavesN7_21S5
