import Jsp000404.SevenLowerFixedCutGroup10Part00
import Jsp000404.SevenLowerFixedCutGroup10Part01
import Jsp000404.SevenLowerFixedCutGroup10Part02
import Jsp000404.SevenLowerFixedCutGroup10Part03
import Jsp000404.SevenLowerFixedCutGroup10Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup10
open SevenLowerReplay
def contexts : Fin 10 → Context := ![SevenLowerFixedCutContexts.context300, SevenLowerFixedCutContexts.context301, SevenLowerFixedCutContexts.context303, SevenLowerFixedCutContexts.context304, SevenLowerFixedCutContexts.context308, SevenLowerFixedCutContexts.context309, SevenLowerFixedCutContexts.context310, SevenLowerFixedCutContexts.context311, SevenLowerFixedCutContexts.context315, SevenLowerFixedCutContexts.context316]
def fuels : Fin 10 → ℕ := ![16, 17, 18, 18, 17, 17, 18, 19, 19, 19]
def ids : Fin 10 → ℕ := ![7705, 7801, 7853, 7916, 7967, 8021, 8104, 8248, 8285, 8344]

theorem cuts_checked : ∀ j : Fin 10,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup10Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup10Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup10Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup10Part01.cuts_checked 2
  · exact SevenLowerFixedCutGroup10Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup10Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup10Part02.cuts_checked 2
  · exact SevenLowerFixedCutGroup10Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup10Part03.cuts_checked 1
  · exact SevenLowerFixedCutGroup10Part04.cuts_checked 0

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup10
