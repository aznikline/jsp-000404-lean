import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup04Part02
open SevenLowerReplay
def contexts : Fin 9 → Context := ![SevenLowerFixedCutContexts.context131, SevenLowerFixedCutContexts.context132, SevenLowerFixedCutContexts.context133, SevenLowerFixedCutContexts.context134, SevenLowerFixedCutContexts.context135, SevenLowerFixedCutContexts.context136, SevenLowerFixedCutContexts.context137, SevenLowerFixedCutContexts.context138, SevenLowerFixedCutContexts.context139]
def fuels : Fin 9 → ℕ := ![18, 18, 18, 18, 18, 18, 18, 18, 18]
def ids : Fin 9 → ℕ := ![3376, 3377, 3378, 3379, 3380, 3434, 3467, 3468, 3469]

theorem cuts_checked : ∀ j : Fin 9,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup04Part02
