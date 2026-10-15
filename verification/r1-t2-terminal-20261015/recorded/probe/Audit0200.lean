import Lean
import Jsp000404.R1LeavesN7_55S14
import Jsp000404.R1LeavesN7_55S15
import Jsp000404.R1LeavesN7_62S8
import Jsp000404.R1LeavesN7_62S9
import Jsp000404.R1LeavesN7_73S8
import Jsp000404.R1LeavesN7_73S9
import Jsp000404.R1LeavesN7_77S11
import Jsp000404.R1LeavesN7_78S10
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
#localaudit Jsp000404.R1LeavesN7_55S14
#localaudit Jsp000404.R1LeavesN7_55S15
#localaudit Jsp000404.R1LeavesN7_62S8
#localaudit Jsp000404.R1LeavesN7_62S9
#localaudit Jsp000404.R1LeavesN7_73S8
#localaudit Jsp000404.R1LeavesN7_73S9
#localaudit Jsp000404.R1LeavesN7_77S11
#localaudit Jsp000404.R1LeavesN7_78S10
