import Lean
import Jsp000404.R1LeavesN7_40S9
import Jsp000404.R1LeavesN7_40S11
import Jsp000404.R1LeavesN7_41S9
import Jsp000404.R1LeavesN7_41S10
import Jsp000404.R1LeavesN7_41S11
import Jsp000404.R1LeavesN7_41S12
import Jsp000404.R1LeavesN7_41S13
import Jsp000404.R1LeavesN7_41S14
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
#localaudit Jsp000404.R1LeavesN7_40S9
#localaudit Jsp000404.R1LeavesN7_40S11
#localaudit Jsp000404.R1LeavesN7_41S9
#localaudit Jsp000404.R1LeavesN7_41S10
#localaudit Jsp000404.R1LeavesN7_41S11
#localaudit Jsp000404.R1LeavesN7_41S12
#localaudit Jsp000404.R1LeavesN7_41S13
#localaudit Jsp000404.R1LeavesN7_41S14
