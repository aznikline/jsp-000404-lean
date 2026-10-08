import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup01Part00
open SevenLowerReplay
def contexts : Fin 4 → Context := ![SevenLowerFixedCutContexts.context032, SevenLowerFixedCutContexts.context033, SevenLowerFixedCutContexts.context034, SevenLowerFixedCutContexts.context035]
def fuels : Fin 4 → ℕ := ![13, 15, 15, 15]
def ids : Fin 4 → ℕ := ![999, 1002, 1003, 1004]

theorem cuts_checked : ∀ j : Fin 4,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup01Part00
