import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup05Part03
open SevenLowerReplay
def contexts : Fin 1 → Context := ![SevenLowerFixedCutContexts.context195]
def fuels : Fin 1 → ℕ := ![19]
def ids : Fin 1 → ℕ := ![4423]

theorem cuts_checked : ∀ j : Fin 1,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup05Part03
