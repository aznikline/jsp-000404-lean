import Jsp000404.SevenLowerFixedCutGroup12Part00
import Jsp000404.SevenLowerFixedCutGroup12Part01
import Jsp000404.SevenLowerFixedCutGroup12Part02
import Jsp000404.SevenLowerFixedCutGroup12Part03
import Jsp000404.SevenLowerFixedCutGroup12Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup12
open SevenLowerReplay
def contexts : Fin 12 → Context := ![SevenLowerFixedCutContexts.context350, SevenLowerFixedCutContexts.context351, SevenLowerFixedCutContexts.context354, SevenLowerFixedCutContexts.context355, SevenLowerFixedCutContexts.context356, SevenLowerFixedCutContexts.context358, SevenLowerFixedCutContexts.context359, SevenLowerFixedCutContexts.context363, SevenLowerFixedCutContexts.context364, SevenLowerFixedCutContexts.context365, SevenLowerFixedCutContexts.context366, SevenLowerFixedCutContexts.context369]
def fuels : Fin 12 → ℕ := ![17, 18, 17, 17, 18, 19, 19, 18, 18, 19, 20, 20]
def ids : Fin 12 → ℕ := ![9297, 9359, 9407, 9458, 9525, 9592, 9662, 9729, 9792, 9915, 10032, 10104]

theorem cuts_checked : ∀ j : Fin 12,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup12Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup12Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup12Part00.cuts_checked 2
  · exact SevenLowerFixedCutGroup12Part00.cuts_checked 3
  · exact SevenLowerFixedCutGroup12Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup12Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup12Part01.cuts_checked 2
  · exact SevenLowerFixedCutGroup12Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup12Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup12Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup12Part04.cuts_checked 0
  · exact SevenLowerFixedCutGroup12Part04.cuts_checked 1

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup12
