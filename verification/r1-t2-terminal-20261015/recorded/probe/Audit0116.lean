import Lean
import Jsp000404.R1LeavesN7_7S1
import Jsp000404.R1LeavesN7_7S10
import Jsp000404.R1LeavesN7_7S9
import Jsp000404.R1LeavesN7_7S11
import Jsp000404.R1LeavesN7_7S12
import Jsp000404.R1LeavesN7_7S13
import Jsp000404.R1LeavesN7_7S14
import Jsp000404.R1LeavesN7_7S2
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
#localaudit Jsp000404.R1LeavesN7_7S1
#localaudit Jsp000404.R1LeavesN7_7S10
#localaudit Jsp000404.R1LeavesN7_7S9
#localaudit Jsp000404.R1LeavesN7_7S11
#localaudit Jsp000404.R1LeavesN7_7S12
#localaudit Jsp000404.R1LeavesN7_7S13
#localaudit Jsp000404.R1LeavesN7_7S14
#localaudit Jsp000404.R1LeavesN7_7S2
