import Lean
import Jsp000404.R1LeavesN7_21S23
import Jsp000404.R1LeavesN7_21S24
import Jsp000404.R1LeavesN7_23S0
import Jsp000404.R1LeavesN7_23S1
import Jsp000404.R1LeavesN7_23S5
import Jsp000404.R1LeavesN7_23S6
import Jsp000404.R1LeavesN7_23S7
import Jsp000404.R1LeavesN7_23S8
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
#localaudit Jsp000404.R1LeavesN7_21S23
#localaudit Jsp000404.R1LeavesN7_21S24
#localaudit Jsp000404.R1LeavesN7_23S0
#localaudit Jsp000404.R1LeavesN7_23S1
#localaudit Jsp000404.R1LeavesN7_23S5
#localaudit Jsp000404.R1LeavesN7_23S6
#localaudit Jsp000404.R1LeavesN7_23S7
#localaudit Jsp000404.R1LeavesN7_23S8
