import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup05Part01
open SevenLowerReplay
def contexts : Fin 16 → Context := ![SevenLowerFixedCutContexts.context170, SevenLowerFixedCutContexts.context171, SevenLowerFixedCutContexts.context172, SevenLowerFixedCutContexts.context173, SevenLowerFixedCutContexts.context174, SevenLowerFixedCutContexts.context175, SevenLowerFixedCutContexts.context176, SevenLowerFixedCutContexts.context177, SevenLowerFixedCutContexts.context178, SevenLowerFixedCutContexts.context179, SevenLowerFixedCutContexts.context180, SevenLowerFixedCutContexts.context181, SevenLowerFixedCutContexts.context182, SevenLowerFixedCutContexts.context188, SevenLowerFixedCutContexts.context189, SevenLowerFixedCutContexts.context190]
def fuels : Fin 16 → ℕ := ![19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 18, 18, 19]
def ids : Fin 16 → ℕ := ![3942, 3943, 3954, 3955, 3956, 3957, 3958, 3959, 3960, 3961, 3962, 3963, 3964, 4040, 4099, 4138]

theorem cuts_checked : ∀ j : Fin 16,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup05Part01
