import Jsp000404.SevenLowerReplay

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchPilot
open SevenLowerReplay
def firstCycle : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![(-3), (0), (0), (3), (-1), (-1)]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0 (![1, 2, 3, 4, 5]), .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 10 0, .triangle 0 0]

def firstContext : Context :=
  ⟨![(some false), (some false), (some false), (some false), (some false), (some false), (some false), (some false), (some false), (some false), (some false), none, none, none, none, none, none, none, none, none], (some 0), ![none, none, none, none]⟩

theorem first_cycle_checked : firstCycle.check firstContext = true := by decide

#print axioms first_cycle_checked
end Jsp404.SevenLowerBranchPilot
