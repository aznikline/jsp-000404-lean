import Lean
import Jsp000404.R1LeavesN7_83S4
import Jsp000404.R1CertT2_10_12_23
import Jsp000404.R1LeavesN7_0S0
import Jsp000404.R1LeavesN7_0S1
import Jsp000404.R1LeavesN7_0S7
import Jsp000404.R1LeavesN7_0S8
import Jsp000404.R1LeavesN7_0S9
import Jsp000404.R1LeavesN7_0S10
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
#localaudit Jsp000404.R1LeavesN7_83S4
#localaudit Jsp000404.R1CertT2_10_12_23
#localaudit Jsp000404.R1LeavesN7_0S0
#localaudit Jsp000404.R1LeavesN7_0S1
#localaudit Jsp000404.R1LeavesN7_0S7
#localaudit Jsp000404.R1LeavesN7_0S8
#localaudit Jsp000404.R1LeavesN7_0S9
#localaudit Jsp000404.R1LeavesN7_0S10
