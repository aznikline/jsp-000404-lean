import Lean
import Jsp000404.R1LeavesN7_1S48
import Jsp000404.R1LeavesN7_1S49
import Jsp000404.R1LeavesN7_1S50
import Jsp000404.R1LeavesN7_1S51
import Jsp000404.R1LeavesN7_1S52
import Jsp000404.R1LeavesN7_1S53
import Jsp000404.R1LeavesN7_1S54
import Jsp000404.R1LeavesN7_1S55
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
#localaudit Jsp000404.R1LeavesN7_1S48
#localaudit Jsp000404.R1LeavesN7_1S49
#localaudit Jsp000404.R1LeavesN7_1S50
#localaudit Jsp000404.R1LeavesN7_1S51
#localaudit Jsp000404.R1LeavesN7_1S52
#localaudit Jsp000404.R1LeavesN7_1S53
#localaudit Jsp000404.R1LeavesN7_1S54
#localaudit Jsp000404.R1LeavesN7_1S55
