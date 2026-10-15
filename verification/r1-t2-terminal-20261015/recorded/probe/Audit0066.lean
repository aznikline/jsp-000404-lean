import Lean
import Jsp000404.R1LeavesN7_2S44
import Jsp000404.R1LeavesN7_2S45
import Jsp000404.R1LeavesN7_2S46
import Jsp000404.R1LeavesN7_2S47
import Jsp000404.R1LeavesN7_2S48
import Jsp000404.R1LeavesN7_2S49
import Jsp000404.R1LeavesN7_2S50
import Jsp000404.R1LeavesN7_2S51
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
#localaudit Jsp000404.R1LeavesN7_2S44
#localaudit Jsp000404.R1LeavesN7_2S45
#localaudit Jsp000404.R1LeavesN7_2S46
#localaudit Jsp000404.R1LeavesN7_2S47
#localaudit Jsp000404.R1LeavesN7_2S48
#localaudit Jsp000404.R1LeavesN7_2S49
#localaudit Jsp000404.R1LeavesN7_2S50
#localaudit Jsp000404.R1LeavesN7_2S51
