import Lean
import Jsp000404.R1LeavesN7_0S78
import Jsp000404.R1LeavesN7_0S79
import Jsp000404.R1LeavesN7_0S80
import Jsp000404.R1LeavesN7_0S81
import Jsp000404.R1LeavesN7_0S82
import Jsp000404.R1LeavesN7_0S83
import Jsp000404.R1LeavesN7_0S84
import Jsp000404.R1LeavesN7_0S85
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
#localaudit Jsp000404.R1LeavesN7_0S78
#localaudit Jsp000404.R1LeavesN7_0S79
#localaudit Jsp000404.R1LeavesN7_0S80
#localaudit Jsp000404.R1LeavesN7_0S81
#localaudit Jsp000404.R1LeavesN7_0S82
#localaudit Jsp000404.R1LeavesN7_0S83
#localaudit Jsp000404.R1LeavesN7_0S84
#localaudit Jsp000404.R1LeavesN7_0S85
