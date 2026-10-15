import Lean
import Jsp000404.R1LeavesN7_59S13
import Jsp000404.R1LeavesN7_60S7
import Jsp000404.R1LeavesN7_60S8
import Jsp000404.R1LeavesN7_60S9
import Jsp000404.R1LeavesN7_61S8
import Jsp000404.R1LeavesN7_61S9
import Jsp000404.R1LeavesN7_61S10
import Jsp000404.R1LeavesN7_61S11
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
#localaudit Jsp000404.R1LeavesN7_59S13
#localaudit Jsp000404.R1LeavesN7_60S7
#localaudit Jsp000404.R1LeavesN7_60S8
#localaudit Jsp000404.R1LeavesN7_60S9
#localaudit Jsp000404.R1LeavesN7_61S8
#localaudit Jsp000404.R1LeavesN7_61S9
#localaudit Jsp000404.R1LeavesN7_61S10
#localaudit Jsp000404.R1LeavesN7_61S11
