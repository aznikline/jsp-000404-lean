import Lean
import Jsp000404.R1LeavesN7_2S28
import Jsp000404.R1LeavesN7_2S29
import Jsp000404.R1LeavesN7_2S30
import Jsp000404.R1LeavesN7_2S31
import Jsp000404.R1LeavesN7_2S32
import Jsp000404.R1LeavesN7_2S33
import Jsp000404.R1LeavesN7_2S34
import Jsp000404.R1LeavesN7_2S35
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
#localaudit Jsp000404.R1LeavesN7_2S28
#localaudit Jsp000404.R1LeavesN7_2S29
#localaudit Jsp000404.R1LeavesN7_2S30
#localaudit Jsp000404.R1LeavesN7_2S31
#localaudit Jsp000404.R1LeavesN7_2S32
#localaudit Jsp000404.R1LeavesN7_2S33
#localaudit Jsp000404.R1LeavesN7_2S34
#localaudit Jsp000404.R1LeavesN7_2S35
