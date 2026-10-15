import Lean
import Jsp000404.R1LeavesN7_42S14
import Jsp000404.R1LeavesN7_44S10
import Jsp000404.R1LeavesN7_44S11
import Jsp000404.R1LeavesN7_44S12
import Jsp000404.R1LeavesN7_44S13
import Jsp000404.R1LeavesN7_61S12
import Jsp000404.R1LeavesN7_61S13
import Jsp000404.R1LeavesN7_62S10
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
#localaudit Jsp000404.R1LeavesN7_42S14
#localaudit Jsp000404.R1LeavesN7_44S10
#localaudit Jsp000404.R1LeavesN7_44S11
#localaudit Jsp000404.R1LeavesN7_44S12
#localaudit Jsp000404.R1LeavesN7_44S13
#localaudit Jsp000404.R1LeavesN7_61S12
#localaudit Jsp000404.R1LeavesN7_61S13
#localaudit Jsp000404.R1LeavesN7_62S10
