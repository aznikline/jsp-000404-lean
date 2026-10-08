import Jsp000404.SevenLowerFixedCutGroup05Part00
import Jsp000404.SevenLowerFixedCutGroup05Part01
import Jsp000404.SevenLowerFixedCutGroup05Part02
import Jsp000404.SevenLowerFixedCutGroup05Part03
import Jsp000404.SevenLowerFixedCutGroup05Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup05
open SevenLowerReplay
def contexts : Fin 28 → Context := ![SevenLowerFixedCutContexts.context162, SevenLowerFixedCutContexts.context163, SevenLowerFixedCutContexts.context164, SevenLowerFixedCutContexts.context165, SevenLowerFixedCutContexts.context166, SevenLowerFixedCutContexts.context167, SevenLowerFixedCutContexts.context168, SevenLowerFixedCutContexts.context169, SevenLowerFixedCutContexts.context170, SevenLowerFixedCutContexts.context171, SevenLowerFixedCutContexts.context172, SevenLowerFixedCutContexts.context173, SevenLowerFixedCutContexts.context174, SevenLowerFixedCutContexts.context175, SevenLowerFixedCutContexts.context176, SevenLowerFixedCutContexts.context177, SevenLowerFixedCutContexts.context178, SevenLowerFixedCutContexts.context179, SevenLowerFixedCutContexts.context180, SevenLowerFixedCutContexts.context181, SevenLowerFixedCutContexts.context182, SevenLowerFixedCutContexts.context188, SevenLowerFixedCutContexts.context189, SevenLowerFixedCutContexts.context190, SevenLowerFixedCutContexts.context193, SevenLowerFixedCutContexts.context194, SevenLowerFixedCutContexts.context195, SevenLowerFixedCutContexts.context197]
def fuels : Fin 28 → ℕ := ![19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 18, 18, 19, 18, 18, 19, 20]
def ids : Fin 28 → ℕ := ![3869, 3870, 3871, 3872, 3873, 3874, 3875, 3915, 3942, 3943, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3962, 3963, 3964, 4040, 4099, 4138, 4193, 4274, 4423, 4475]

theorem cuts_checked : ∀ j : Fin 28,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup05Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup05Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup05Part00.cuts_checked 2
  · exact SevenLowerFixedCutGroup05Part00.cuts_checked 3
  · exact SevenLowerFixedCutGroup05Part00.cuts_checked 4
  · exact SevenLowerFixedCutGroup05Part00.cuts_checked 5
  · exact SevenLowerFixedCutGroup05Part00.cuts_checked 6
  · exact SevenLowerFixedCutGroup05Part00.cuts_checked 7
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 2
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 3
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 4
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 5
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 6
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 7
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 8
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 9
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 10
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 11
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 12
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 13
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 14
  · exact SevenLowerFixedCutGroup05Part01.cuts_checked 15
  · exact SevenLowerFixedCutGroup05Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup05Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup05Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup05Part04.cuts_checked 0

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup05
