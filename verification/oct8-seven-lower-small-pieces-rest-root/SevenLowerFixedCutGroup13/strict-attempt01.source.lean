import Jsp000404.SevenLowerFixedCutGroup13Part00
import Jsp000404.SevenLowerFixedCutGroup13Part01
import Jsp000404.SevenLowerFixedCutGroup13Part02
import Jsp000404.SevenLowerFixedCutGroup13Part03
import Jsp000404.SevenLowerFixedCutGroup13Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup13
open SevenLowerReplay
def contexts : Fin 7 → Context := ![SevenLowerFixedCutContexts.context370, SevenLowerFixedCutContexts.context371, SevenLowerFixedCutContexts.context376, SevenLowerFixedCutContexts.context377, SevenLowerFixedCutContexts.context378, SevenLowerFixedCutContexts.context379, SevenLowerFixedCutContexts.context380]
def fuels : Fin 7 → ℕ := ![20, 21, 19, 19, 20, 21, 22]
def ids : Fin 7 → ℕ := ![10190, 10280, 10350, 10425, 10510, 10650, 10809]

theorem cuts_checked : ∀ j : Fin 7,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup13Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup13Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup13Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup13Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup13Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup13Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup13Part04.cuts_checked 0

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup13
