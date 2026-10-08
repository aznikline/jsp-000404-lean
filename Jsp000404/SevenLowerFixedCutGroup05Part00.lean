import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup05Part00
open SevenLowerReplay
def contexts : Fin 8 → Context := ![SevenLowerFixedCutContexts.context162, SevenLowerFixedCutContexts.context163, SevenLowerFixedCutContexts.context164, SevenLowerFixedCutContexts.context165, SevenLowerFixedCutContexts.context166, SevenLowerFixedCutContexts.context167, SevenLowerFixedCutContexts.context168, SevenLowerFixedCutContexts.context169]
def fuels : Fin 8 → ℕ := ![19, 19, 19, 19, 19, 19, 19, 19]
def ids : Fin 8 → ℕ := ![3869, 3870, 3871, 3872, 3873, 3874, 3875, 3915]

theorem cuts_checked : ∀ j : Fin 8,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup05Part00
