import Lean
import Jsp000404.Base3
import Jsp000404.Basic
import Jsp000404.GC
import Jsp000404.Sector
import Jsp000404.SectorOS
import Jsp000404.EvenPartition
import Jsp000404.SectorBound
import Jsp000404.WingBound
import Jsp000404.CrossCircle
import Jsp000404.CircleBound
import Jsp000404.Staircase
import Jsp000404.Section4Legality
import Jsp000404.Deletion
import Jsp000404.GeometricDeletion
import Jsp000404.Base3Bridge
import Jsp000404.Induction
import Jsp000404.ConeCorridor
import JSP404.BinaryEncoding
import Jsp000404.IntervalPacking
import Jsp000404.AnchoredRows
import JSP404.Basic
import JSP404.DirectionalCover
import Jsp000404.BinGraphs
import Jsp000404.ChartInvariance
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
#localaudit Jsp000404.Base3
#localaudit Jsp000404.Basic
#localaudit Jsp000404.GC
#localaudit Jsp000404.Sector
#localaudit Jsp000404.SectorOS
#localaudit Jsp000404.EvenPartition
#localaudit Jsp000404.SectorBound
#localaudit Jsp000404.WingBound
#localaudit Jsp000404.CrossCircle
#localaudit Jsp000404.CircleBound
#localaudit Jsp000404.Staircase
#localaudit Jsp000404.Section4Legality
#localaudit Jsp000404.Deletion
#localaudit Jsp000404.GeometricDeletion
#localaudit Jsp000404.Base3Bridge
#localaudit Jsp000404.Induction
#localaudit Jsp000404.ConeCorridor
#localaudit JSP404.BinaryEncoding
#localaudit Jsp000404.IntervalPacking
#localaudit Jsp000404.AnchoredRows
#localaudit JSP404.Basic
#localaudit JSP404.DirectionalCover
#localaudit Jsp000404.BinGraphs
#localaudit Jsp000404.ChartInvariance
