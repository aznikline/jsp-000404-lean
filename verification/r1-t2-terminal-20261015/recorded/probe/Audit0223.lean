import Lean
import Jsp000404.MixedTwoInHelpers
import Jsp000404.MixedTwoInCentralCore
import Jsp000404.MixedTwoInOuterLow
import Jsp000404.MixedTwoInOuterHigh
import Jsp000404.MixedTwoInCentral
import Jsp000404.SameSideTwoIn
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
#localaudit Jsp000404.MixedTwoInHelpers
#localaudit Jsp000404.MixedTwoInCentralCore
#localaudit Jsp000404.MixedTwoInOuterLow
#localaudit Jsp000404.MixedTwoInOuterHigh
#localaudit Jsp000404.MixedTwoInCentral
#localaudit Jsp000404.SameSideTwoIn
