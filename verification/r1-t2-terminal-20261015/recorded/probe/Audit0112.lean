import Lean
import Jsp000404.R1LeavesN7_41S15
import Jsp000404.R1LeavesN7_41S16
import Jsp000404.R1LeavesN7_41S17
import Jsp000404.R1LeavesN7_45S0
import Jsp000404.R1LeavesN7_45S1
import Jsp000404.R1LeavesN7_45S2
import Jsp000404.R1LeavesN7_45S3
import Jsp000404.R1LeavesN7_45S4
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
#localaudit Jsp000404.R1LeavesN7_41S15
#localaudit Jsp000404.R1LeavesN7_41S16
#localaudit Jsp000404.R1LeavesN7_41S17
#localaudit Jsp000404.R1LeavesN7_45S0
#localaudit Jsp000404.R1LeavesN7_45S1
#localaudit Jsp000404.R1LeavesN7_45S2
#localaudit Jsp000404.R1LeavesN7_45S3
#localaudit Jsp000404.R1LeavesN7_45S4
