import Lean
import Jsp000404.R1LeavesN7_1S40
import Jsp000404.R1LeavesN7_1S41
import Jsp000404.R1LeavesN7_1S42
import Jsp000404.R1LeavesN7_1S43
import Jsp000404.R1LeavesN7_1S44
import Jsp000404.R1LeavesN7_1S45
import Jsp000404.R1LeavesN7_1S46
import Jsp000404.R1LeavesN7_1S47
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
#localaudit Jsp000404.R1LeavesN7_1S40
#localaudit Jsp000404.R1LeavesN7_1S41
#localaudit Jsp000404.R1LeavesN7_1S42
#localaudit Jsp000404.R1LeavesN7_1S43
#localaudit Jsp000404.R1LeavesN7_1S44
#localaudit Jsp000404.R1LeavesN7_1S45
#localaudit Jsp000404.R1LeavesN7_1S46
#localaudit Jsp000404.R1LeavesN7_1S47
