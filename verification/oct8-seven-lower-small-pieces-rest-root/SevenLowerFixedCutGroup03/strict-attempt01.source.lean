import Jsp000404.SevenLowerFixedCutGroup03Part00
import Jsp000404.SevenLowerFixedCutGroup03Part01
import Jsp000404.SevenLowerFixedCutGroup03Part02
import Jsp000404.SevenLowerFixedCutGroup03Part03
import Jsp000404.SevenLowerFixedCutGroup03Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup03
open SevenLowerReplay
def contexts : Fin 28 → Context := ![SevenLowerFixedCutContexts.context091, SevenLowerFixedCutContexts.context092, SevenLowerFixedCutContexts.context093, SevenLowerFixedCutContexts.context096, SevenLowerFixedCutContexts.context098, SevenLowerFixedCutContexts.context099, SevenLowerFixedCutContexts.context100, SevenLowerFixedCutContexts.context101, SevenLowerFixedCutContexts.context102, SevenLowerFixedCutContexts.context103, SevenLowerFixedCutContexts.context104, SevenLowerFixedCutContexts.context105, SevenLowerFixedCutContexts.context106, SevenLowerFixedCutContexts.context107, SevenLowerFixedCutContexts.context108, SevenLowerFixedCutContexts.context109, SevenLowerFixedCutContexts.context110, SevenLowerFixedCutContexts.context111, SevenLowerFixedCutContexts.context112, SevenLowerFixedCutContexts.context113, SevenLowerFixedCutContexts.context114, SevenLowerFixedCutContexts.context115, SevenLowerFixedCutContexts.context116, SevenLowerFixedCutContexts.context117, SevenLowerFixedCutContexts.context118, SevenLowerFixedCutContexts.context119, SevenLowerFixedCutContexts.context121, SevenLowerFixedCutContexts.context122]
def fuels : Fin 28 → ℕ := ![16, 16, 17, 16, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 17, 18, 18]
def ids : Fin 28 → ℕ := ![2337, 2431, 2515, 2619, 2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630, 2663, 2752, 2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831, 2832, 2833, 2955, 3007, 3051]

theorem cuts_checked : ∀ j : Fin 28,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup03Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup03Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 2
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 3
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 4
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 5
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 6
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 7
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 8
  · exact SevenLowerFixedCutGroup03Part01.cuts_checked 9
  · exact SevenLowerFixedCutGroup03Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup03Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 1
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 2
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 3
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 4
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 5
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 6
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 7
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 8
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 9
  · exact SevenLowerFixedCutGroup03Part03.cuts_checked 10
  · exact SevenLowerFixedCutGroup03Part04.cuts_checked 0
  · exact SevenLowerFixedCutGroup03Part04.cuts_checked 1
  · exact SevenLowerFixedCutGroup03Part04.cuts_checked 2

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup03
