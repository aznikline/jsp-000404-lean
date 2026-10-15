import Lean
import Jsp000404.R1LeavesN7_70S10
import Jsp000404.R1LeavesN7_70S11
import Jsp000404.R1LeavesN7_71S11
import Jsp000404.R1LeavesN7_71S12
import Jsp000404.R1LeavesN7_81S8
import Jsp000404.R1LeavesN7_84S9
import Jsp000404.R1CertT2_22_14
import Jsp000404.SaturatedNesting
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
#localaudit Jsp000404.R1LeavesN7_70S10
#localaudit Jsp000404.R1LeavesN7_70S11
#localaudit Jsp000404.R1LeavesN7_71S11
#localaudit Jsp000404.R1LeavesN7_71S12
#localaudit Jsp000404.R1LeavesN7_81S8
#localaudit Jsp000404.R1LeavesN7_84S9
#localaudit Jsp000404.R1CertT2_22_14
#localaudit Jsp000404.SaturatedNesting
