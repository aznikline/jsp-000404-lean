import Lean
import Jsp000404.R1LeavesN7_1S24
import Jsp000404.R1LeavesN7_1S25
import Jsp000404.R1LeavesN7_1S26
import Jsp000404.R1LeavesN7_1S27
import Jsp000404.R1LeavesN7_1S28
import Jsp000404.R1LeavesN7_1S29
import Jsp000404.R1LeavesN7_1S30
import Jsp000404.R1LeavesN7_1S31
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
#localaudit Jsp000404.R1LeavesN7_1S24
#localaudit Jsp000404.R1LeavesN7_1S25
#localaudit Jsp000404.R1LeavesN7_1S26
#localaudit Jsp000404.R1LeavesN7_1S27
#localaudit Jsp000404.R1LeavesN7_1S28
#localaudit Jsp000404.R1LeavesN7_1S29
#localaudit Jsp000404.R1LeavesN7_1S30
#localaudit Jsp000404.R1LeavesN7_1S31
