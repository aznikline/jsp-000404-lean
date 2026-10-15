import Lean
import Jsp000404.R1LeavesN7_71S6
import Jsp000404.R1LeavesN7_72S2
import Jsp000404.R1LeavesN7_73S1
import Jsp000404.R1LeavesN7_73S2
import Jsp000404.R1LeavesN7_74S3
import Jsp000404.R1LeavesN7_74S4
import Jsp000404.R1LeavesN7_76S2
import Jsp000404.R1LeavesN7_76S3
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
#localaudit Jsp000404.R1LeavesN7_71S6
#localaudit Jsp000404.R1LeavesN7_72S2
#localaudit Jsp000404.R1LeavesN7_73S1
#localaudit Jsp000404.R1LeavesN7_73S2
#localaudit Jsp000404.R1LeavesN7_74S3
#localaudit Jsp000404.R1LeavesN7_74S4
#localaudit Jsp000404.R1LeavesN7_76S2
#localaudit Jsp000404.R1LeavesN7_76S3
