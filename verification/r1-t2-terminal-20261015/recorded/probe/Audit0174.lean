import Lean
import Jsp000404.R1LeavesN7_48S5
import Jsp000404.R1LeavesN7_48S6
import Jsp000404.R1LeavesN7_48S7
import Jsp000404.R1LeavesN7_48S8
import Jsp000404.R1LeavesN7_52S11
import Jsp000404.R1LeavesN7_52S12
import Jsp000404.R1LeavesN7_52S13
import Jsp000404.R1LeavesN7_52S14
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
#localaudit Jsp000404.R1LeavesN7_48S5
#localaudit Jsp000404.R1LeavesN7_48S6
#localaudit Jsp000404.R1LeavesN7_48S7
#localaudit Jsp000404.R1LeavesN7_48S8
#localaudit Jsp000404.R1LeavesN7_52S11
#localaudit Jsp000404.R1LeavesN7_52S12
#localaudit Jsp000404.R1LeavesN7_52S13
#localaudit Jsp000404.R1LeavesN7_52S14
