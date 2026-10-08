import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup03Part03
open SevenLowerReplay
def contexts : Fin 11 → Context := ![SevenLowerFixedCutContexts.context108, SevenLowerFixedCutContexts.context109, SevenLowerFixedCutContexts.context110, SevenLowerFixedCutContexts.context111, SevenLowerFixedCutContexts.context112, SevenLowerFixedCutContexts.context113, SevenLowerFixedCutContexts.context114, SevenLowerFixedCutContexts.context115, SevenLowerFixedCutContexts.context116, SevenLowerFixedCutContexts.context117, SevenLowerFixedCutContexts.context118]
def fuels : Fin 11 → ℕ := ![15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15]
def ids : Fin 11 → ℕ := ![2823, 2824, 2825, 2826, 2827, 2828, 2829, 2830, 2831, 2832, 2833]

theorem cuts_checked : ∀ j : Fin 11,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup03Part03
