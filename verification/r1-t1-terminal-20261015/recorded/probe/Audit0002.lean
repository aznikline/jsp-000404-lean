import Lean
import Jsp000404.R1LeavesN7_64S5
import Jsp000404.R1LeavesN7_64S6
import Jsp000404.R1CertT1_20_12_14
import Jsp000404.R1CertT1_21_15
import Jsp000404.R1CertT1_22_14
import Jsp000404.R1DispatchT1
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
#localaudit Jsp000404.R1LeavesN7_64S5
#localaudit Jsp000404.R1LeavesN7_64S6
#localaudit Jsp000404.R1CertT1_20_12_14
#localaudit Jsp000404.R1CertT1_21_15
#localaudit Jsp000404.R1CertT1_22_14
#localaudit Jsp000404.R1DispatchT1
