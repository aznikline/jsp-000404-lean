import Lean
import Jsp000404.R1LeavesN7_6S27
import Jsp000404.R1LeavesN7_6S28
import Jsp000404.R1LeavesN7_6S29
import Jsp000404.R1LeavesN7_6S30
import Jsp000404.R1LeavesN7_72S9
import Jsp000404.R1LeavesN7_80S10
import Jsp000404.R1LeavesN7_80S9
import Jsp000404.R1LeavesN7_82S9
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
#localaudit Jsp000404.R1LeavesN7_6S27
#localaudit Jsp000404.R1LeavesN7_6S28
#localaudit Jsp000404.R1LeavesN7_6S29
#localaudit Jsp000404.R1LeavesN7_6S30
#localaudit Jsp000404.R1LeavesN7_72S9
#localaudit Jsp000404.R1LeavesN7_80S10
#localaudit Jsp000404.R1LeavesN7_80S9
#localaudit Jsp000404.R1LeavesN7_82S9
