import Lean
import Jsp000404.R1LeavesN7_0S30
import Jsp000404.R1LeavesN7_0S31
import Jsp000404.R1LeavesN7_0S32
import Jsp000404.R1LeavesN7_0S33
import Jsp000404.R1LeavesN7_0S34
import Jsp000404.R1LeavesN7_0S35
import Jsp000404.R1LeavesN7_0S36
import Jsp000404.R1LeavesN7_0S37
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
#localaudit Jsp000404.R1LeavesN7_0S30
#localaudit Jsp000404.R1LeavesN7_0S31
#localaudit Jsp000404.R1LeavesN7_0S32
#localaudit Jsp000404.R1LeavesN7_0S33
#localaudit Jsp000404.R1LeavesN7_0S34
#localaudit Jsp000404.R1LeavesN7_0S35
#localaudit Jsp000404.R1LeavesN7_0S36
#localaudit Jsp000404.R1LeavesN7_0S37
