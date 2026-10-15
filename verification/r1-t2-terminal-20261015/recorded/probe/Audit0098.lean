import Lean
import Jsp000404.R1LeavesN7_69S4
import Jsp000404.R1LeavesN7_69S5
import Jsp000404.R1LeavesN7_69S6
import Jsp000404.R1LeavesN7_69S7
import Jsp000404.R1LeavesN7_70S3
import Jsp000404.R1LeavesN7_70S4
import Jsp000404.R1LeavesN7_71S4
import Jsp000404.R1LeavesN7_71S5
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
#localaudit Jsp000404.R1LeavesN7_69S4
#localaudit Jsp000404.R1LeavesN7_69S5
#localaudit Jsp000404.R1LeavesN7_69S6
#localaudit Jsp000404.R1LeavesN7_69S7
#localaudit Jsp000404.R1LeavesN7_70S3
#localaudit Jsp000404.R1LeavesN7_70S4
#localaudit Jsp000404.R1LeavesN7_71S4
#localaudit Jsp000404.R1LeavesN7_71S5
