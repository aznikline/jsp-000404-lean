import Lean
import Jsp000404.R1LeavesN7_48S3
import Jsp000404.R1LeavesN7_50S0
import Jsp000404.R1LeavesN7_50S1
import Jsp000404.R1LeavesN7_50S10
import Jsp000404.R1LeavesN7_50S7
import Jsp000404.R1LeavesN7_50S8
import Jsp000404.R1LeavesN7_50S9
import Jsp000404.R1LeavesN7_50S11
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
#localaudit Jsp000404.R1LeavesN7_48S3
#localaudit Jsp000404.R1LeavesN7_50S0
#localaudit Jsp000404.R1LeavesN7_50S1
#localaudit Jsp000404.R1LeavesN7_50S10
#localaudit Jsp000404.R1LeavesN7_50S7
#localaudit Jsp000404.R1LeavesN7_50S8
#localaudit Jsp000404.R1LeavesN7_50S9
#localaudit Jsp000404.R1LeavesN7_50S11
