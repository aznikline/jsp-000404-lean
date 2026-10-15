import Lean
import Jsp000404.R1LeavesN7_2S10
import Jsp000404.R1LeavesN7_2S2
import Jsp000404.R1LeavesN7_2S3
import Jsp000404.R1LeavesN7_2S4
import Jsp000404.R1LeavesN7_2S5
import Jsp000404.R1LeavesN7_2S6
import Jsp000404.R1LeavesN7_2S7
import Jsp000404.R1LeavesN7_2S11
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
#localaudit Jsp000404.R1LeavesN7_2S10
#localaudit Jsp000404.R1LeavesN7_2S2
#localaudit Jsp000404.R1LeavesN7_2S3
#localaudit Jsp000404.R1LeavesN7_2S4
#localaudit Jsp000404.R1LeavesN7_2S5
#localaudit Jsp000404.R1LeavesN7_2S6
#localaudit Jsp000404.R1LeavesN7_2S7
#localaudit Jsp000404.R1LeavesN7_2S11
