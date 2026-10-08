import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup12Part00
open SevenLowerReplay
def contexts : Fin 4 → Context := ![SevenLowerFixedCutContexts.context350, SevenLowerFixedCutContexts.context351, SevenLowerFixedCutContexts.context354, SevenLowerFixedCutContexts.context355]
def fuels : Fin 4 → ℕ := ![17, 18, 17, 17]
def ids : Fin 4 → ℕ := ![9297, 9359, 9407, 9458]

theorem cuts_checked : ∀ j : Fin 4,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup12Part00
