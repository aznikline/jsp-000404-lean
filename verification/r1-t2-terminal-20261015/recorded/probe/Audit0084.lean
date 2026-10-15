import Lean
import Jsp000404.R1LeavesN7_12S11
import Jsp000404.R1LeavesN7_12S12
import Jsp000404.R1LeavesN7_12S13
import Jsp000404.R1LeavesN7_12S14
import Jsp000404.R1LeavesN7_12S15
import Jsp000404.R1LeavesN7_12S16
import Jsp000404.R1LeavesN7_12S2
import Jsp000404.R1LeavesN7_12S3
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
#localaudit Jsp000404.R1LeavesN7_12S11
#localaudit Jsp000404.R1LeavesN7_12S12
#localaudit Jsp000404.R1LeavesN7_12S13
#localaudit Jsp000404.R1LeavesN7_12S14
#localaudit Jsp000404.R1LeavesN7_12S15
#localaudit Jsp000404.R1LeavesN7_12S16
#localaudit Jsp000404.R1LeavesN7_12S2
#localaudit Jsp000404.R1LeavesN7_12S3
