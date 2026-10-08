import Jsp000404.SevenLowerFixedCutGroup04Part00
import Jsp000404.SevenLowerFixedCutGroup04Part01
import Jsp000404.SevenLowerFixedCutGroup04Part02
import Jsp000404.SevenLowerFixedCutGroup04Part03
import Jsp000404.SevenLowerFixedCutGroup04Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup04
open SevenLowerReplay
def contexts : Fin 29 → Context := ![SevenLowerFixedCutContexts.context126, SevenLowerFixedCutContexts.context127, SevenLowerFixedCutContexts.context128, SevenLowerFixedCutContexts.context130, SevenLowerFixedCutContexts.context131, SevenLowerFixedCutContexts.context132, SevenLowerFixedCutContexts.context133, SevenLowerFixedCutContexts.context134, SevenLowerFixedCutContexts.context135, SevenLowerFixedCutContexts.context136, SevenLowerFixedCutContexts.context137, SevenLowerFixedCutContexts.context138, SevenLowerFixedCutContexts.context139, SevenLowerFixedCutContexts.context140, SevenLowerFixedCutContexts.context141, SevenLowerFixedCutContexts.context142, SevenLowerFixedCutContexts.context143, SevenLowerFixedCutContexts.context144, SevenLowerFixedCutContexts.context145, SevenLowerFixedCutContexts.context146, SevenLowerFixedCutContexts.context147, SevenLowerFixedCutContexts.context148, SevenLowerFixedCutContexts.context149, SevenLowerFixedCutContexts.context150, SevenLowerFixedCutContexts.context154, SevenLowerFixedCutContexts.context155, SevenLowerFixedCutContexts.context156, SevenLowerFixedCutContexts.context159, SevenLowerFixedCutContexts.context160]
def fuels : Fin 29 → ℕ := ![17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 20, 19, 19]
def ids : Fin 29 → ℕ := ![3118, 3170, 3289, 3346, 3376, 3377, 3378, 3379, 3380, 3434, 3467, 3468, 3469, 3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495, 3571, 3630, 3669, 3724, 3807]

theorem cuts_checked : ∀ j : Fin 29,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup04Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup04Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup04Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup04Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup04Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup04Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup04Part02.cuts_checked 2
  · exact SevenLowerFixedCutGroup04Part02.cuts_checked 3
  · exact SevenLowerFixedCutGroup04Part02.cuts_checked 4
  · exact SevenLowerFixedCutGroup04Part02.cuts_checked 5
  · exact SevenLowerFixedCutGroup04Part02.cuts_checked 6
  · exact SevenLowerFixedCutGroup04Part02.cuts_checked 7
  · exact SevenLowerFixedCutGroup04Part02.cuts_checked 8
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 1
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 2
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 3
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 4
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 5
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 6
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 7
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 8
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 9
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 10
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 11
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 12
  · exact SevenLowerFixedCutGroup04Part03.cuts_checked 13
  · exact SevenLowerFixedCutGroup04Part04.cuts_checked 0
  · exact SevenLowerFixedCutGroup04Part04.cuts_checked 1

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup04
