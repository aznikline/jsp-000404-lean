import Lean
import Jsp000404.R1LeavesN7_77S4
import Jsp000404.R1LeavesN7_77S5
import Jsp000404.R1LeavesN7_78S3
import Jsp000404.R1LeavesN7_79S6
import Jsp000404.R1LeavesN7_79S7
import Jsp000404.R1LeavesN7_79S8
import Jsp000404.R1LeavesN7_80S3
import Jsp000404.R1LeavesN7_81S2
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
#localaudit Jsp000404.R1LeavesN7_77S4
#localaudit Jsp000404.R1LeavesN7_77S5
#localaudit Jsp000404.R1LeavesN7_78S3
#localaudit Jsp000404.R1LeavesN7_79S6
#localaudit Jsp000404.R1LeavesN7_79S7
#localaudit Jsp000404.R1LeavesN7_79S8
#localaudit Jsp000404.R1LeavesN7_80S3
#localaudit Jsp000404.R1LeavesN7_81S2
