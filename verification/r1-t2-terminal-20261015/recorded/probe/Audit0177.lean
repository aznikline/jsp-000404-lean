import Lean
import Jsp000404.R1LeavesN7_57S13
import Jsp000404.R1LeavesN7_57S14
import Jsp000404.R1LeavesN7_58S10
import Jsp000404.R1LeavesN7_58S11
import Jsp000404.R1LeavesN7_58S12
import Jsp000404.R1LeavesN7_58S13
import Jsp000404.R1LeavesN7_59S11
import Jsp000404.R1LeavesN7_59S12
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
#localaudit Jsp000404.R1LeavesN7_57S13
#localaudit Jsp000404.R1LeavesN7_57S14
#localaudit Jsp000404.R1LeavesN7_58S10
#localaudit Jsp000404.R1LeavesN7_58S11
#localaudit Jsp000404.R1LeavesN7_58S12
#localaudit Jsp000404.R1LeavesN7_58S13
#localaudit Jsp000404.R1LeavesN7_59S11
#localaudit Jsp000404.R1LeavesN7_59S12
