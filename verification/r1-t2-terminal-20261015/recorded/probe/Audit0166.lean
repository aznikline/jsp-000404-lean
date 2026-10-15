import Lean
import Jsp000404.R1LeavesN7_25S13
import Jsp000404.R1LeavesN7_25S14
import Jsp000404.R1LeavesN7_25S15
import Jsp000404.R1LeavesN7_25S16
import Jsp000404.R1LeavesN7_25S17
import Jsp000404.R1LeavesN7_25S18
import Jsp000404.R1LeavesN7_25S19
import Jsp000404.R1LeavesN7_25S20
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
#localaudit Jsp000404.R1LeavesN7_25S13
#localaudit Jsp000404.R1LeavesN7_25S14
#localaudit Jsp000404.R1LeavesN7_25S15
#localaudit Jsp000404.R1LeavesN7_25S16
#localaudit Jsp000404.R1LeavesN7_25S17
#localaudit Jsp000404.R1LeavesN7_25S18
#localaudit Jsp000404.R1LeavesN7_25S19
#localaudit Jsp000404.R1LeavesN7_25S20
