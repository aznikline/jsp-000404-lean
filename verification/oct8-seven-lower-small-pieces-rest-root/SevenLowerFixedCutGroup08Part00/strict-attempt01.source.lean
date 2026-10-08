import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup08Part00
open SevenLowerReplay
def contexts : Fin 3 → Context := ![SevenLowerFixedCutContexts.context271, SevenLowerFixedCutContexts.context272, SevenLowerFixedCutContexts.context273]
def fuels : Fin 3 → ℕ := ![16, 16, 17]
def ids : Fin 3 → ℕ := ![6115, 6187, 6227]

theorem cuts_checked : ∀ j : Fin 3,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup08Part00
