import Lean
import Jsp000404.R1LeavesN7_75S2
import Jsp000404.R1LeavesN7_76S0
import Jsp000404.R1LeavesN7_77S0
import Jsp000404.R1LeavesN7_77S1
import Jsp000404.R1LeavesN7_78S0
import Jsp000404.R1LeavesN7_78S1
import Jsp000404.R1LeavesN7_79S0
import Jsp000404.R1LeavesN7_79S1
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
#localaudit Jsp000404.R1LeavesN7_75S2
#localaudit Jsp000404.R1LeavesN7_76S0
#localaudit Jsp000404.R1LeavesN7_77S0
#localaudit Jsp000404.R1LeavesN7_77S1
#localaudit Jsp000404.R1LeavesN7_78S0
#localaudit Jsp000404.R1LeavesN7_78S1
#localaudit Jsp000404.R1LeavesN7_79S0
#localaudit Jsp000404.R1LeavesN7_79S1
