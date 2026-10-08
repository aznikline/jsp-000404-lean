import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup11Part02
open SevenLowerReplay
def contexts : Fin 3 → Context := ![SevenLowerFixedCutContexts.context330, SevenLowerFixedCutContexts.context333, SevenLowerFixedCutContexts.context334]
def fuels : Fin 3 → ℕ := ![19, 18, 18]
def ids : Fin 3 → ℕ := ![8758, 8813, 8872]

theorem cuts_checked : ∀ j : Fin 3,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup11Part02
