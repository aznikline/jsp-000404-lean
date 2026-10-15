import Lean
import Jsp000404.R1LeavesN7_2S36
import Jsp000404.R1LeavesN7_2S37
import Jsp000404.R1LeavesN7_2S38
import Jsp000404.R1LeavesN7_2S39
import Jsp000404.R1LeavesN7_2S40
import Jsp000404.R1LeavesN7_2S41
import Jsp000404.R1LeavesN7_2S42
import Jsp000404.R1LeavesN7_2S43
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
#localaudit Jsp000404.R1LeavesN7_2S36
#localaudit Jsp000404.R1LeavesN7_2S37
#localaudit Jsp000404.R1LeavesN7_2S38
#localaudit Jsp000404.R1LeavesN7_2S39
#localaudit Jsp000404.R1LeavesN7_2S40
#localaudit Jsp000404.R1LeavesN7_2S41
#localaudit Jsp000404.R1LeavesN7_2S42
#localaudit Jsp000404.R1LeavesN7_2S43
