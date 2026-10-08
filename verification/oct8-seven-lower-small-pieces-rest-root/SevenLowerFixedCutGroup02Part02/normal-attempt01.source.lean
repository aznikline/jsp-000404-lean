import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup02Part02
open SevenLowerReplay
def contexts : Fin 13 → Context := ![SevenLowerFixedCutContexts.context065, SevenLowerFixedCutContexts.context066, SevenLowerFixedCutContexts.context067, SevenLowerFixedCutContexts.context068, SevenLowerFixedCutContexts.context069, SevenLowerFixedCutContexts.context070, SevenLowerFixedCutContexts.context071, SevenLowerFixedCutContexts.context072, SevenLowerFixedCutContexts.context073, SevenLowerFixedCutContexts.context074, SevenLowerFixedCutContexts.context075, SevenLowerFixedCutContexts.context077, SevenLowerFixedCutContexts.context078]
def fuels : Fin 13 → ℕ := ![16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 18, 18]
def ids : Fin 13 → ℕ := ![1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1930, 2003]

theorem cuts_checked : ∀ j : Fin 13,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup02Part02
