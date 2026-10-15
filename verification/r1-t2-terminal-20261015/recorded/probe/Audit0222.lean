import Lean
import Jsp000404.DeletionRigidityCore
import Jsp000404.DeletionRigidityGaps
import Jsp000404.DeletionRigidityRows
import Jsp000404.DeletionRigidityFivePoint
import Jsp000404.DeletionRigidityReceivers
import Jsp000404.DeletionRigidityHighPotential
import Jsp000404.DeletionRigidityFacing
import Jsp000404.DeletionRigidity
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
#localaudit Jsp000404.DeletionRigidityCore
#localaudit Jsp000404.DeletionRigidityGaps
#localaudit Jsp000404.DeletionRigidityRows
#localaudit Jsp000404.DeletionRigidityFivePoint
#localaudit Jsp000404.DeletionRigidityReceivers
#localaudit Jsp000404.DeletionRigidityHighPotential
#localaudit Jsp000404.DeletionRigidityFacing
#localaudit Jsp000404.DeletionRigidity
