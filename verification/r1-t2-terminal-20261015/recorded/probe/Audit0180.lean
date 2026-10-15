import Lean
import Jsp000404.R1LeavesN7_67S3
import Jsp000404.R1LeavesN7_67S4
import Jsp000404.R1LeavesN7_67S5
import Jsp000404.R1LeavesN7_67S6
import Jsp000404.R1LeavesN7_68S12
import Jsp000404.R1LeavesN7_68S13
import Jsp000404.R1LeavesN7_68S14
import Jsp000404.R1LeavesN7_69S10
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
#localaudit Jsp000404.R1LeavesN7_67S3
#localaudit Jsp000404.R1LeavesN7_67S4
#localaudit Jsp000404.R1LeavesN7_67S5
#localaudit Jsp000404.R1LeavesN7_67S6
#localaudit Jsp000404.R1LeavesN7_68S12
#localaudit Jsp000404.R1LeavesN7_68S13
#localaudit Jsp000404.R1LeavesN7_68S14
#localaudit Jsp000404.R1LeavesN7_69S10
