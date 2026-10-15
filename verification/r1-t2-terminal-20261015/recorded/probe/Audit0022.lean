import Lean
import Jsp000404.R1LeavesN7_11S18
import Jsp000404.R1LeavesN7_11S19
import Jsp000404.R1LeavesN7_11S20
import Jsp000404.R1LeavesN7_11S21
import Jsp000404.R1LeavesN7_11S22
import Jsp000404.R1LeavesN7_11S23
import Jsp000404.R1LeavesN7_11S24
import Jsp000404.R1LeavesN7_11S25
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
#localaudit Jsp000404.R1LeavesN7_11S18
#localaudit Jsp000404.R1LeavesN7_11S19
#localaudit Jsp000404.R1LeavesN7_11S20
#localaudit Jsp000404.R1LeavesN7_11S21
#localaudit Jsp000404.R1LeavesN7_11S22
#localaudit Jsp000404.R1LeavesN7_11S23
#localaudit Jsp000404.R1LeavesN7_11S24
#localaudit Jsp000404.R1LeavesN7_11S25
