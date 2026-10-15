import Lean
import Jsp000404.R1LeavesN7_71S2
import Jsp000404.R1LeavesN7_71S3
import Jsp000404.R1LeavesN7_72S0
import Jsp000404.R1LeavesN7_72S1
import Jsp000404.R1LeavesN7_73S0
import Jsp000404.R1LeavesN7_74S0
import Jsp000404.R1LeavesN7_74S1
import Jsp000404.R1LeavesN7_74S2
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
#localaudit Jsp000404.R1LeavesN7_71S2
#localaudit Jsp000404.R1LeavesN7_71S3
#localaudit Jsp000404.R1LeavesN7_72S0
#localaudit Jsp000404.R1LeavesN7_72S1
#localaudit Jsp000404.R1LeavesN7_73S0
#localaudit Jsp000404.R1LeavesN7_74S0
#localaudit Jsp000404.R1LeavesN7_74S1
#localaudit Jsp000404.R1LeavesN7_74S2
