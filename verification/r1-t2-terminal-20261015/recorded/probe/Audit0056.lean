import Lean
import Jsp000404.R1LeavesN7_8S20
import Jsp000404.R1LeavesN7_8S21
import Jsp000404.R1LeavesN7_8S22
import Jsp000404.R1LeavesN7_8S23
import Jsp000404.R1LeavesN7_8S24
import Jsp000404.R1LeavesN7_8S25
import Jsp000404.R1CertT2_10_12_13_25
import Jsp000404.R1LeavesN7_24S0
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
#localaudit Jsp000404.R1LeavesN7_8S20
#localaudit Jsp000404.R1LeavesN7_8S21
#localaudit Jsp000404.R1LeavesN7_8S22
#localaudit Jsp000404.R1LeavesN7_8S23
#localaudit Jsp000404.R1LeavesN7_8S24
#localaudit Jsp000404.R1LeavesN7_8S25
#localaudit Jsp000404.R1CertT2_10_12_13_25
#localaudit Jsp000404.R1LeavesN7_24S0
