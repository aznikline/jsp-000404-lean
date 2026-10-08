import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup13Part01
open SevenLowerReplay
def contexts : Fin 2 → Context := ![SevenLowerFixedCutContexts.context376, SevenLowerFixedCutContexts.context377]
def fuels : Fin 2 → ℕ := ![19, 19]
def ids : Fin 2 → ℕ := ![10350, 10425]

theorem cuts_checked : ∀ j : Fin 2,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup13Part01
