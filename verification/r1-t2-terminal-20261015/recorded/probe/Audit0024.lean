import Lean
import Jsp000404.R1LeavesN7_1S5
import Jsp000404.R1LeavesN7_1S6
import Jsp000404.R1LeavesN7_1S7
import Jsp000404.R1LeavesN7_1S8
import Jsp000404.R1LeavesN7_1S12
import Jsp000404.R1LeavesN7_1S13
import Jsp000404.R1LeavesN7_1S14
import Jsp000404.R1LeavesN7_1S15
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
#localaudit Jsp000404.R1LeavesN7_1S5
#localaudit Jsp000404.R1LeavesN7_1S6
#localaudit Jsp000404.R1LeavesN7_1S7
#localaudit Jsp000404.R1LeavesN7_1S8
#localaudit Jsp000404.R1LeavesN7_1S12
#localaudit Jsp000404.R1LeavesN7_1S13
#localaudit Jsp000404.R1LeavesN7_1S14
#localaudit Jsp000404.R1LeavesN7_1S15
