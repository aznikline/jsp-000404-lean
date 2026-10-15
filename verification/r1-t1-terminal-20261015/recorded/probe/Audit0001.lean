import Lean
import Jsp000404.R1LeavesN7_36S17
import Jsp000404.R1LeavesN7_36S18
import Jsp000404.R1LeavesN7_36S19
import Jsp000404.R1LeavesN7_36S20
import Jsp000404.R1LeavesN7_48S9
import Jsp000404.R1LeavesN7_48S10
import Jsp000404.R1LeavesN7_48S11
import Jsp000404.R1LeavesN7_48S12
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
#localaudit Jsp000404.R1LeavesN7_36S17
#localaudit Jsp000404.R1LeavesN7_36S18
#localaudit Jsp000404.R1LeavesN7_36S19
#localaudit Jsp000404.R1LeavesN7_36S20
#localaudit Jsp000404.R1LeavesN7_48S9
#localaudit Jsp000404.R1LeavesN7_48S10
#localaudit Jsp000404.R1LeavesN7_48S11
#localaudit Jsp000404.R1LeavesN7_48S12
