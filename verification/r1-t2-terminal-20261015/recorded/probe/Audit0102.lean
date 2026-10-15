import Lean
import Jsp000404.R1CertT2_11_12_14_25
import Jsp000404.R1LeavesN7_27S10
import Jsp000404.R1LeavesN7_27S11
import Jsp000404.R1LeavesN7_27S12
import Jsp000404.R1LeavesN7_27S13
import Jsp000404.R1LeavesN7_27S14
import Jsp000404.R1LeavesN7_27S15
import Jsp000404.R1LeavesN7_27S16
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
#localaudit Jsp000404.R1CertT2_11_12_14_25
#localaudit Jsp000404.R1LeavesN7_27S10
#localaudit Jsp000404.R1LeavesN7_27S11
#localaudit Jsp000404.R1LeavesN7_27S12
#localaudit Jsp000404.R1LeavesN7_27S13
#localaudit Jsp000404.R1LeavesN7_27S14
#localaudit Jsp000404.R1LeavesN7_27S15
#localaudit Jsp000404.R1LeavesN7_27S16
