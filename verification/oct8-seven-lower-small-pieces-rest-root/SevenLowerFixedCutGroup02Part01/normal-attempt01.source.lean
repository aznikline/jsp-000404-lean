import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup02Part01
open SevenLowerReplay
def contexts : Fin 8 → Context := ![SevenLowerFixedCutContexts.context057, SevenLowerFixedCutContexts.context058, SevenLowerFixedCutContexts.context059, SevenLowerFixedCutContexts.context060, SevenLowerFixedCutContexts.context061, SevenLowerFixedCutContexts.context062, SevenLowerFixedCutContexts.context063, SevenLowerFixedCutContexts.context064]
def fuels : Fin 8 → ℕ := ![16, 16, 16, 16, 16, 16, 16, 16]
def ids : Fin 8 → ℕ := ![1738, 1739, 1740, 1741, 1742, 1783, 1808, 1809]

theorem cuts_checked : ∀ j : Fin 8,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup02Part01
