import Lean
import Jsp000404.R1LeavesN7_2S20
import Jsp000404.R1LeavesN7_2S21
import Jsp000404.R1LeavesN7_2S22
import Jsp000404.R1LeavesN7_2S23
import Jsp000404.R1LeavesN7_2S24
import Jsp000404.R1LeavesN7_2S25
import Jsp000404.R1LeavesN7_2S26
import Jsp000404.R1LeavesN7_2S27
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
#localaudit Jsp000404.R1LeavesN7_2S20
#localaudit Jsp000404.R1LeavesN7_2S21
#localaudit Jsp000404.R1LeavesN7_2S22
#localaudit Jsp000404.R1LeavesN7_2S23
#localaudit Jsp000404.R1LeavesN7_2S24
#localaudit Jsp000404.R1LeavesN7_2S25
#localaudit Jsp000404.R1LeavesN7_2S26
#localaudit Jsp000404.R1LeavesN7_2S27
