import Lean
import Jsp000404.R1LeavesN7_0S62
import Jsp000404.R1LeavesN7_0S63
import Jsp000404.R1LeavesN7_0S64
import Jsp000404.R1LeavesN7_0S65
import Jsp000404.R1LeavesN7_0S66
import Jsp000404.R1LeavesN7_0S67
import Jsp000404.R1LeavesN7_0S68
import Jsp000404.R1LeavesN7_0S69
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
#localaudit Jsp000404.R1LeavesN7_0S62
#localaudit Jsp000404.R1LeavesN7_0S63
#localaudit Jsp000404.R1LeavesN7_0S64
#localaudit Jsp000404.R1LeavesN7_0S65
#localaudit Jsp000404.R1LeavesN7_0S66
#localaudit Jsp000404.R1LeavesN7_0S67
#localaudit Jsp000404.R1LeavesN7_0S68
#localaudit Jsp000404.R1LeavesN7_0S69
