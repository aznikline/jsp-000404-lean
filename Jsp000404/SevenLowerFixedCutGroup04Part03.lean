import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup04Part03
open SevenLowerReplay
def contexts : Fin 14 → Context := ![SevenLowerFixedCutContexts.context140, SevenLowerFixedCutContexts.context141, SevenLowerFixedCutContexts.context142, SevenLowerFixedCutContexts.context143, SevenLowerFixedCutContexts.context144, SevenLowerFixedCutContexts.context145, SevenLowerFixedCutContexts.context146, SevenLowerFixedCutContexts.context147, SevenLowerFixedCutContexts.context148, SevenLowerFixedCutContexts.context149, SevenLowerFixedCutContexts.context150, SevenLowerFixedCutContexts.context154, SevenLowerFixedCutContexts.context155, SevenLowerFixedCutContexts.context156]
def fuels : Fin 14 → ℕ := ![18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 20]
def ids : Fin 14 → ℕ := ![3485, 3486, 3487, 3488, 3489, 3490, 3491, 3492, 3493, 3494, 3495, 3571, 3630, 3669]

theorem cuts_checked : ∀ j : Fin 14,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup04Part03
