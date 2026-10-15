import Lean
import Jsp000404.R1LeavesN7_31S13
import Jsp000404.R1LeavesN7_31S14
import Jsp000404.R1LeavesN7_49S12
import Jsp000404.R1LeavesN7_49S13
import Jsp000404.R1LeavesN7_49S14
import Jsp000404.R1LeavesN7_49S15
import Jsp000404.R1LeavesN7_55S12
import Jsp000404.R1LeavesN7_55S13
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
#localaudit Jsp000404.R1LeavesN7_31S13
#localaudit Jsp000404.R1LeavesN7_31S14
#localaudit Jsp000404.R1LeavesN7_49S12
#localaudit Jsp000404.R1LeavesN7_49S13
#localaudit Jsp000404.R1LeavesN7_49S14
#localaudit Jsp000404.R1LeavesN7_49S15
#localaudit Jsp000404.R1LeavesN7_55S12
#localaudit Jsp000404.R1LeavesN7_55S13
