import Lean
import Jsp000404.R1LeavesN7_63S4
import Jsp000404.R1LeavesN7_63S5
import Jsp000404.R1LeavesN7_63S6
import Jsp000404.R1LeavesN7_71S7
import Jsp000404.R1LeavesN7_74S5
import Jsp000404.R1LeavesN7_75S3
import Jsp000404.R1LeavesN7_77S3
import Jsp000404.R1LeavesN7_7S0
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
#localaudit Jsp000404.R1LeavesN7_63S4
#localaudit Jsp000404.R1LeavesN7_63S5
#localaudit Jsp000404.R1LeavesN7_63S6
#localaudit Jsp000404.R1LeavesN7_71S7
#localaudit Jsp000404.R1LeavesN7_74S5
#localaudit Jsp000404.R1LeavesN7_75S3
#localaudit Jsp000404.R1LeavesN7_77S3
#localaudit Jsp000404.R1LeavesN7_7S0
