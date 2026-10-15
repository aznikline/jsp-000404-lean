import Lean
import Jsp000404.R1LeavesN7_58S1
import Jsp000404.R1LeavesN7_59S0
import Jsp000404.R1LeavesN7_59S1
import Jsp000404.R1LeavesN7_61S0
import Jsp000404.R1LeavesN7_61S1
import Jsp000404.R1LeavesN7_61S2
import Jsp000404.R1LeavesN7_61S3
import Jsp000404.R1LeavesN7_61S4
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
#localaudit Jsp000404.R1LeavesN7_58S1
#localaudit Jsp000404.R1LeavesN7_59S0
#localaudit Jsp000404.R1LeavesN7_59S1
#localaudit Jsp000404.R1LeavesN7_61S0
#localaudit Jsp000404.R1LeavesN7_61S1
#localaudit Jsp000404.R1LeavesN7_61S2
#localaudit Jsp000404.R1LeavesN7_61S3
#localaudit Jsp000404.R1LeavesN7_61S4
