import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup07Part03
open SevenLowerReplay
def contexts : Fin 4 → Context := ![SevenLowerFixedCutContexts.context251, SevenLowerFixedCutContexts.context252, SevenLowerFixedCutContexts.context257, SevenLowerFixedCutContexts.context258]
def fuels : Fin 4 → ℕ := ![20, 21, 19, 19]
def ids : Fin 4 → ℕ := ![5742, 5793, 5823, 5874]

theorem cuts_checked : ∀ j : Fin 4,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup07Part03
