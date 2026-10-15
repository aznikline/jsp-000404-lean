import Lean
import Jsp000404.R1LeavesN7_0S54
import Jsp000404.R1LeavesN7_0S55
import Jsp000404.R1LeavesN7_0S56
import Jsp000404.R1LeavesN7_0S57
import Jsp000404.R1LeavesN7_0S58
import Jsp000404.R1LeavesN7_0S59
import Jsp000404.R1LeavesN7_0S60
import Jsp000404.R1LeavesN7_0S61
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
#localaudit Jsp000404.R1LeavesN7_0S54
#localaudit Jsp000404.R1LeavesN7_0S55
#localaudit Jsp000404.R1LeavesN7_0S56
#localaudit Jsp000404.R1LeavesN7_0S57
#localaudit Jsp000404.R1LeavesN7_0S58
#localaudit Jsp000404.R1LeavesN7_0S59
#localaudit Jsp000404.R1LeavesN7_0S60
#localaudit Jsp000404.R1LeavesN7_0S61
