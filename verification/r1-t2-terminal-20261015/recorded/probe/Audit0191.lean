import Lean
import Jsp000404.R1LeavesN7_66S11
import Jsp000404.R1LeavesN7_67S9
import Jsp000404.R1LeavesN7_67S10
import Jsp000404.R1LeavesN7_67S7
import Jsp000404.R1LeavesN7_67S8
import Jsp000404.R1LeavesN7_6S0
import Jsp000404.R1LeavesN7_6S1
import Jsp000404.R1LeavesN7_6S2
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
#localaudit Jsp000404.R1LeavesN7_66S11
#localaudit Jsp000404.R1LeavesN7_67S9
#localaudit Jsp000404.R1LeavesN7_67S10
#localaudit Jsp000404.R1LeavesN7_67S7
#localaudit Jsp000404.R1LeavesN7_67S8
#localaudit Jsp000404.R1LeavesN7_6S0
#localaudit Jsp000404.R1LeavesN7_6S1
#localaudit Jsp000404.R1LeavesN7_6S2
