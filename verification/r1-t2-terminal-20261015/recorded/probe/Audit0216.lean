import Lean
import Jsp000404.R1LeavesN7_76S9
import Jsp000404.R1LeavesN7_80S11
import Jsp000404.R1LeavesN7_82S10
import Jsp000404.R1LeavesN7_83S10
import Jsp000404.R1LeavesN7_83S9
import Jsp000404.R1LeavesN7_86S8
import Jsp000404.R1CertT2_22_13_15
import Jsp000404.R1LeavesN7_20S0
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
#localaudit Jsp000404.R1LeavesN7_76S9
#localaudit Jsp000404.R1LeavesN7_80S11
#localaudit Jsp000404.R1LeavesN7_82S10
#localaudit Jsp000404.R1LeavesN7_83S10
#localaudit Jsp000404.R1LeavesN7_83S9
#localaudit Jsp000404.R1LeavesN7_86S8
#localaudit Jsp000404.R1CertT2_22_13_15
#localaudit Jsp000404.R1LeavesN7_20S0
