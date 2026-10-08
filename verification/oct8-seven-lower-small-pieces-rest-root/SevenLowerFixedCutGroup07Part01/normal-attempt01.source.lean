import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup07Part01
open SevenLowerReplay
def contexts : Fin 1 → Context := ![SevenLowerFixedCutContexts.context245]
def fuels : Fin 1 → ℕ := ![18]
def ids : Fin 1 → ℕ := ![5502]

theorem cuts_checked : ∀ j : Fin 1,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup07Part01
