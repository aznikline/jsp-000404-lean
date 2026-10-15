import Lean
import Jsp000404.R1LeavesN7_78S7
import Jsp000404.R1LeavesN7_78S8
import Jsp000404.R1LeavesN7_80S7
import Jsp000404.R1LeavesN7_80S8
import Jsp000404.R1LeavesN7_81S7
import Jsp000404.R1LeavesN7_82S7
import Jsp000404.R1LeavesN7_82S8
import Jsp000404.R1LeavesN7_84S6
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
#localaudit Jsp000404.R1LeavesN7_78S7
#localaudit Jsp000404.R1LeavesN7_78S8
#localaudit Jsp000404.R1LeavesN7_80S7
#localaudit Jsp000404.R1LeavesN7_80S8
#localaudit Jsp000404.R1LeavesN7_81S7
#localaudit Jsp000404.R1LeavesN7_82S7
#localaudit Jsp000404.R1LeavesN7_82S8
#localaudit Jsp000404.R1LeavesN7_84S6
