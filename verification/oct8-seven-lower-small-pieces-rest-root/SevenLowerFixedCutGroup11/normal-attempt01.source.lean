import Jsp000404.SevenLowerFixedCutGroup11Part00
import Jsp000404.SevenLowerFixedCutGroup11Part01
import Jsp000404.SevenLowerFixedCutGroup11Part02
import Jsp000404.SevenLowerFixedCutGroup11Part03
import Jsp000404.SevenLowerFixedCutGroup11Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup11
open SevenLowerReplay
def contexts : Fin 15 → Context := ![SevenLowerFixedCutContexts.context317, SevenLowerFixedCutContexts.context320, SevenLowerFixedCutContexts.context321, SevenLowerFixedCutContexts.context322, SevenLowerFixedCutContexts.context328, SevenLowerFixedCutContexts.context329, SevenLowerFixedCutContexts.context330, SevenLowerFixedCutContexts.context333, SevenLowerFixedCutContexts.context334, SevenLowerFixedCutContexts.context335, SevenLowerFixedCutContexts.context337, SevenLowerFixedCutContexts.context338, SevenLowerFixedCutContexts.context340, SevenLowerFixedCutContexts.context341, SevenLowerFixedCutContexts.context349]
def fuels : Fin 15 → ℕ := ![20, 19, 19, 20, 18, 18, 19, 18, 18, 19, 20, 20, 21, 21, 17]
def ids : Fin 15 → ℕ := ![8405, 8459, 8522, 8600, 8637, 8696, 8758, 8813, 8872, 8945, 9013, 9078, 9130, 9204, 9238]

theorem cuts_checked : ∀ j : Fin 15,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup11Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup11Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup11Part00.cuts_checked 2
  · exact SevenLowerFixedCutGroup11Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup11Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup11Part01.cuts_checked 2
  · exact SevenLowerFixedCutGroup11Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup11Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup11Part02.cuts_checked 2
  · exact SevenLowerFixedCutGroup11Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup11Part03.cuts_checked 1
  · exact SevenLowerFixedCutGroup11Part03.cuts_checked 2
  · exact SevenLowerFixedCutGroup11Part04.cuts_checked 0
  · exact SevenLowerFixedCutGroup11Part04.cuts_checked 1
  · exact SevenLowerFixedCutGroup11Part04.cuts_checked 2

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup11
