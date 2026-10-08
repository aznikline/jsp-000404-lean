import Jsp000404.SevenLowerFixedCutGroup09Part00
import Jsp000404.SevenLowerFixedCutGroup09Part01
import Jsp000404.SevenLowerFixedCutGroup09Part02
import Jsp000404.SevenLowerFixedCutGroup09Part03
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup09
open SevenLowerReplay
def contexts : Fin 8 → Context := ![SevenLowerFixedCutContexts.context285, SevenLowerFixedCutContexts.context286, SevenLowerFixedCutContexts.context287, SevenLowerFixedCutContexts.context288, SevenLowerFixedCutContexts.context294, SevenLowerFixedCutContexts.context295, SevenLowerFixedCutContexts.context296, SevenLowerFixedCutContexts.context299]
def fuels : Fin 8 → ℕ := ![17, 17, 18, 19, 16, 16, 17, 16]
def ids : Fin 8 → ℕ := ![6842, 6963, 7113, 7178, 7250, 7350, 7461, 7562]

theorem cuts_checked : ∀ j : Fin 8,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup09Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup09Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup09Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup09Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup09Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup09Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup09Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup09Part03.cuts_checked 1

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup09
