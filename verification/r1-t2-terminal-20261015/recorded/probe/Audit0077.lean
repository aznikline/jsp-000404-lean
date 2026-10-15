import Lean
import Jsp000404.R1LeavesN7_0S38
import Jsp000404.R1LeavesN7_0S39
import Jsp000404.R1LeavesN7_0S40
import Jsp000404.R1LeavesN7_0S41
import Jsp000404.R1LeavesN7_0S42
import Jsp000404.R1LeavesN7_0S43
import Jsp000404.R1LeavesN7_0S44
import Jsp000404.R1LeavesN7_0S45
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
#localaudit Jsp000404.R1LeavesN7_0S38
#localaudit Jsp000404.R1LeavesN7_0S39
#localaudit Jsp000404.R1LeavesN7_0S40
#localaudit Jsp000404.R1LeavesN7_0S41
#localaudit Jsp000404.R1LeavesN7_0S42
#localaudit Jsp000404.R1LeavesN7_0S43
#localaudit Jsp000404.R1LeavesN7_0S44
#localaudit Jsp000404.R1LeavesN7_0S45
