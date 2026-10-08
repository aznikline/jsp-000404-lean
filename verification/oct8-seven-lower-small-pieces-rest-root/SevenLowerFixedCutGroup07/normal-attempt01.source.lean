import Jsp000404.SevenLowerFixedCutGroup07Part00
import Jsp000404.SevenLowerFixedCutGroup07Part01
import Jsp000404.SevenLowerFixedCutGroup07Part02
import Jsp000404.SevenLowerFixedCutGroup07Part03
import Jsp000404.SevenLowerFixedCutGroup07Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup07
open SevenLowerReplay
def contexts : Fin 13 → Context := ![SevenLowerFixedCutContexts.context240, SevenLowerFixedCutContexts.context244, SevenLowerFixedCutContexts.context245, SevenLowerFixedCutContexts.context246, SevenLowerFixedCutContexts.context247, SevenLowerFixedCutContexts.context250, SevenLowerFixedCutContexts.context251, SevenLowerFixedCutContexts.context252, SevenLowerFixedCutContexts.context257, SevenLowerFixedCutContexts.context258, SevenLowerFixedCutContexts.context259, SevenLowerFixedCutContexts.context260, SevenLowerFixedCutContexts.context261]
def fuels : Fin 13 → ℕ := ![19, 18, 18, 19, 20, 20, 20, 21, 19, 19, 20, 21, 22]
def ids : Fin 13 → ℕ := ![5333, 5385, 5502, 5614, 5664, 5694, 5742, 5793, 5823, 5874, 5921, 5984, 6030]

theorem cuts_checked : ∀ j : Fin 13,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup07Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup07Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup07Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup07Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup07Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup07Part02.cuts_checked 2
  · exact SevenLowerFixedCutGroup07Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup07Part03.cuts_checked 1
  · exact SevenLowerFixedCutGroup07Part03.cuts_checked 2
  · exact SevenLowerFixedCutGroup07Part03.cuts_checked 3
  · exact SevenLowerFixedCutGroup07Part04.cuts_checked 0
  · exact SevenLowerFixedCutGroup07Part04.cuts_checked 1
  · exact SevenLowerFixedCutGroup07Part04.cuts_checked 2

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup07
