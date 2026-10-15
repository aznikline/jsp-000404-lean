import Lean
import Jsp000404.R1LeavesN7_82S1
import Jsp000404.R1LeavesN7_82S2
import Jsp000404.R1LeavesN7_82S6
import Jsp000404.R1LeavesN7_83S0
import Jsp000404.R1LeavesN7_83S1
import Jsp000404.R1LeavesN7_83S6
import Jsp000404.R1LeavesN7_83S7
import Jsp000404.R1LeavesN7_84S0
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
#localaudit Jsp000404.R1LeavesN7_82S1
#localaudit Jsp000404.R1LeavesN7_82S2
#localaudit Jsp000404.R1LeavesN7_82S6
#localaudit Jsp000404.R1LeavesN7_83S0
#localaudit Jsp000404.R1LeavesN7_83S1
#localaudit Jsp000404.R1LeavesN7_83S6
#localaudit Jsp000404.R1LeavesN7_83S7
#localaudit Jsp000404.R1LeavesN7_84S0
