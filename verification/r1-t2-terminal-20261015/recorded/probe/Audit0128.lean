import Lean
import Jsp000404.R1LeavesN7_10S18
import Jsp000404.R1LeavesN7_10S19
import Jsp000404.R1LeavesN7_10S20
import Jsp000404.R1LeavesN7_10S21
import Jsp000404.R1LeavesN7_10S22
import Jsp000404.R1LeavesN7_10S23
import Jsp000404.R1LeavesN7_10S24
import Jsp000404.R1LeavesN7_10S25
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
#localaudit Jsp000404.R1LeavesN7_10S18
#localaudit Jsp000404.R1LeavesN7_10S19
#localaudit Jsp000404.R1LeavesN7_10S20
#localaudit Jsp000404.R1LeavesN7_10S21
#localaudit Jsp000404.R1LeavesN7_10S22
#localaudit Jsp000404.R1LeavesN7_10S23
#localaudit Jsp000404.R1LeavesN7_10S24
#localaudit Jsp000404.R1LeavesN7_10S25
