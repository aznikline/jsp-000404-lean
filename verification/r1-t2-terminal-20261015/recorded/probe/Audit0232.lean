import Lean
import Jsp000404.R3WitnessDag
import Jsp000404.TwoAnchoredRows
import Jsp000404.TwoAnchorAssembly
import Jsp000404.TwoAnchorCorridor
import Jsp000404.Reindex
import Jsp000404.TwoSaturatedHigh
import Jsp000404.FivePointCapacity
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
#localaudit Jsp000404.R3WitnessDag
#localaudit Jsp000404.TwoAnchoredRows
#localaudit Jsp000404.TwoAnchorAssembly
#localaudit Jsp000404.TwoAnchorCorridor
#localaudit Jsp000404.Reindex
#localaudit Jsp000404.TwoSaturatedHigh
#localaudit Jsp000404.FivePointCapacity
