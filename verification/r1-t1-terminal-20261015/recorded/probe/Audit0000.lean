import Lean
import Jsp000404.R1LeavesN7_81S3
import Jsp000404.R1CertT1_11_13_25
import Jsp000404.R1CertT1_11_23
import Jsp000404.R1CertT1_13_24
import Jsp000404.R1LeavesN7_36S13
import Jsp000404.R1LeavesN7_36S14
import Jsp000404.R1LeavesN7_36S15
import Jsp000404.R1LeavesN7_36S16
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
#localaudit Jsp000404.R1LeavesN7_81S3
#localaudit Jsp000404.R1CertT1_11_13_25
#localaudit Jsp000404.R1CertT1_11_23
#localaudit Jsp000404.R1CertT1_13_24
#localaudit Jsp000404.R1LeavesN7_36S13
#localaudit Jsp000404.R1LeavesN7_36S14
#localaudit Jsp000404.R1LeavesN7_36S15
#localaudit Jsp000404.R1LeavesN7_36S16
