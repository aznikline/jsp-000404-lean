import Lean
import Jsp000404.R1LeavesN7_82S3
import Jsp000404.R1LeavesN7_83S5
import Jsp000404.R1LeavesN7_84S1
import Jsp000404.R1LeavesN7_84S2
import Jsp000404.R1LeavesN7_84S3
import Jsp000404.R1LeavesN7_85S2
import Jsp000404.R1LeavesN7_86S2
import Jsp000404.R1LeavesN7_86S4
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
#localaudit Jsp000404.R1LeavesN7_82S3
#localaudit Jsp000404.R1LeavesN7_83S5
#localaudit Jsp000404.R1LeavesN7_84S1
#localaudit Jsp000404.R1LeavesN7_84S2
#localaudit Jsp000404.R1LeavesN7_84S3
#localaudit Jsp000404.R1LeavesN7_85S2
#localaudit Jsp000404.R1LeavesN7_86S2
#localaudit Jsp000404.R1LeavesN7_86S4
