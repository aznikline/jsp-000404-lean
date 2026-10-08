import Jsp000404.SevenLowerFixedCutGroup08Part00
import Jsp000404.SevenLowerFixedCutGroup08Part01
import Jsp000404.SevenLowerFixedCutGroup08Part02
import Jsp000404.SevenLowerFixedCutGroup08Part03
import Jsp000404.SevenLowerFixedCutGroup08Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup08
open SevenLowerReplay
def contexts : Fin 8 → Context := ![SevenLowerFixedCutContexts.context271, SevenLowerFixedCutContexts.context272, SevenLowerFixedCutContexts.context273, SevenLowerFixedCutContexts.context276, SevenLowerFixedCutContexts.context277, SevenLowerFixedCutContexts.context278, SevenLowerFixedCutContexts.context280, SevenLowerFixedCutContexts.context281]
def fuels : Fin 8 → ℕ := ![16, 16, 17, 16, 16, 17, 18, 18]
def ids : Fin 8 → ℕ := ![6115, 6187, 6227, 6288, 6379, 6522, 6589, 6774]

theorem cuts_checked : ∀ j : Fin 8,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup08Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup08Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup08Part00.cuts_checked 2
  · exact SevenLowerFixedCutGroup08Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup08Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup08Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup08Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup08Part04.cuts_checked 0

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup08
