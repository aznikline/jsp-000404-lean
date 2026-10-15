import Lean
import Jsp000404.R1LeavesN7_68S7
import Jsp000404.R1LeavesN7_68S8
import Jsp000404.R1LeavesN7_68S9
import Jsp000404.R1LeavesN7_71S8
import Jsp000404.R1LeavesN7_78S4
import Jsp000404.R1LeavesN7_78S5
import Jsp000404.R1CertT2_12_24
import Jsp000404.R1LeavesN7_26S8
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
#localaudit Jsp000404.R1LeavesN7_68S7
#localaudit Jsp000404.R1LeavesN7_68S8
#localaudit Jsp000404.R1LeavesN7_68S9
#localaudit Jsp000404.R1LeavesN7_71S8
#localaudit Jsp000404.R1LeavesN7_78S4
#localaudit Jsp000404.R1LeavesN7_78S5
#localaudit Jsp000404.R1CertT2_12_24
#localaudit Jsp000404.R1LeavesN7_26S8
