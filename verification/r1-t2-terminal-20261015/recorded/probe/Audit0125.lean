import Lean
import Jsp000404.R1LeavesN7_65S4
import Jsp000404.R1LeavesN7_65S5
import Jsp000404.R1LeavesN7_65S6
import Jsp000404.R1LeavesN7_81S5
import Jsp000404.R1LeavesN7_82S5
import Jsp000404.R1CertT2_11_23
import Jsp000404.R1LeavesN7_10S0
import Jsp000404.R1LeavesN7_10S1
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
#localaudit Jsp000404.R1LeavesN7_65S4
#localaudit Jsp000404.R1LeavesN7_65S5
#localaudit Jsp000404.R1LeavesN7_65S6
#localaudit Jsp000404.R1LeavesN7_81S5
#localaudit Jsp000404.R1LeavesN7_82S5
#localaudit Jsp000404.R1CertT2_11_23
#localaudit Jsp000404.R1LeavesN7_10S0
#localaudit Jsp000404.R1LeavesN7_10S1
