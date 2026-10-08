import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup07Part00
open SevenLowerReplay
def contexts : Fin 2 → Context := ![SevenLowerFixedCutContexts.context240, SevenLowerFixedCutContexts.context244]
def fuels : Fin 2 → ℕ := ![19, 18]
def ids : Fin 2 → ℕ := ![5333, 5385]

theorem cuts_checked : ∀ j : Fin 2,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup07Part00
