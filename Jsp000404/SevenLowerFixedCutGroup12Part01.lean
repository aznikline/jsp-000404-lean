import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup12Part01
open SevenLowerReplay
def contexts : Fin 3 → Context := ![SevenLowerFixedCutContexts.context356, SevenLowerFixedCutContexts.context358, SevenLowerFixedCutContexts.context359]
def fuels : Fin 3 → ℕ := ![18, 19, 19]
def ids : Fin 3 → ℕ := ![9525, 9592, 9662]

theorem cuts_checked : ∀ j : Fin 3,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup12Part01
