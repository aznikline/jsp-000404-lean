import Lean
import Jsp000404.R3WitnessBounds
import Jsp000404.R3WitnessTrichotomy
import Jsp000404.R3WitnessOuter
import Jsp000404.R3WitnessMidTop
import Jsp000404.R3WitnessMidBottom
import Jsp000404.R3WitnessTerminal
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
#localaudit Jsp000404.R3WitnessBounds
#localaudit Jsp000404.R3WitnessTrichotomy
#localaudit Jsp000404.R3WitnessOuter
#localaudit Jsp000404.R3WitnessMidTop
#localaudit Jsp000404.R3WitnessMidBottom
#localaudit Jsp000404.R3WitnessTerminal
