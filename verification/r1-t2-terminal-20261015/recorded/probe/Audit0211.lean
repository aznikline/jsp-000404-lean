import Lean
import Jsp000404.R1LeavesN7_33S9
import Jsp000404.R1LeavesN7_33S10
import Jsp000404.R1LeavesN7_33S11
import Jsp000404.R1LeavesN7_35S6
import Jsp000404.R1LeavesN7_35S7
import Jsp000404.R1LeavesN7_35S8
import Jsp000404.R1LeavesN7_35S9
import Jsp000404.R1LeavesN7_35S10
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
#localaudit Jsp000404.R1LeavesN7_33S9
#localaudit Jsp000404.R1LeavesN7_33S10
#localaudit Jsp000404.R1LeavesN7_33S11
#localaudit Jsp000404.R1LeavesN7_35S6
#localaudit Jsp000404.R1LeavesN7_35S7
#localaudit Jsp000404.R1LeavesN7_35S8
#localaudit Jsp000404.R1LeavesN7_35S9
#localaudit Jsp000404.R1LeavesN7_35S10
