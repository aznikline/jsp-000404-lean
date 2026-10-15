import Lean
import Jsp000404.R1LeavesN7_84S8
import Jsp000404.R1CertT2_20_12_14
import Jsp000404.R1LeavesN7_19S0
import Jsp000404.R1LeavesN7_19S1
import Jsp000404.R1LeavesN7_19S10
import Jsp000404.R1LeavesN7_19S11
import Jsp000404.R1LeavesN7_19S12
import Jsp000404.R1LeavesN7_19S9
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
#localaudit Jsp000404.R1LeavesN7_84S8
#localaudit Jsp000404.R1CertT2_20_12_14
#localaudit Jsp000404.R1LeavesN7_19S0
#localaudit Jsp000404.R1LeavesN7_19S1
#localaudit Jsp000404.R1LeavesN7_19S10
#localaudit Jsp000404.R1LeavesN7_19S11
#localaudit Jsp000404.R1LeavesN7_19S12
#localaudit Jsp000404.R1LeavesN7_19S9
