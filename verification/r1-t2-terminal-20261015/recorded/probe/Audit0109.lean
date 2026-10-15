import Lean
import Jsp000404.R1LeavesN7_3S32
import Jsp000404.R1LeavesN7_3S33
import Jsp000404.R1LeavesN7_3S34
import Jsp000404.R1LeavesN7_3S35
import Jsp000404.R1LeavesN7_3S36
import Jsp000404.R1LeavesN7_3S37
import Jsp000404.R1LeavesN7_3S38
import Jsp000404.R1LeavesN7_3S39
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
#localaudit Jsp000404.R1LeavesN7_3S32
#localaudit Jsp000404.R1LeavesN7_3S33
#localaudit Jsp000404.R1LeavesN7_3S34
#localaudit Jsp000404.R1LeavesN7_3S35
#localaudit Jsp000404.R1LeavesN7_3S36
#localaudit Jsp000404.R1LeavesN7_3S37
#localaudit Jsp000404.R1LeavesN7_3S38
#localaudit Jsp000404.R1LeavesN7_3S39
