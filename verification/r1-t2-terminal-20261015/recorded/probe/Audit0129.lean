import Lean
import Jsp000404.R1LeavesN7_10S26
import Jsp000404.R1LeavesN7_23S12
import Jsp000404.R1LeavesN7_23S13
import Jsp000404.R1LeavesN7_23S14
import Jsp000404.R1LeavesN7_23S15
import Jsp000404.R1LeavesN7_23S16
import Jsp000404.R1LeavesN7_23S17
import Jsp000404.R1LeavesN7_23S18
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
#localaudit Jsp000404.R1LeavesN7_10S26
#localaudit Jsp000404.R1LeavesN7_23S12
#localaudit Jsp000404.R1LeavesN7_23S13
#localaudit Jsp000404.R1LeavesN7_23S14
#localaudit Jsp000404.R1LeavesN7_23S15
#localaudit Jsp000404.R1LeavesN7_23S16
#localaudit Jsp000404.R1LeavesN7_23S17
#localaudit Jsp000404.R1LeavesN7_23S18
