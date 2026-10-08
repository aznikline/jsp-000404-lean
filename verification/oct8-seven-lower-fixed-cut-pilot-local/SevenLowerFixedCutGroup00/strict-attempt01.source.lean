import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup00
open SevenLowerReplay
def contexts : Fin 13 → Context := ![SevenLowerFixedCutContexts.context011, SevenLowerFixedCutContexts.context012, SevenLowerFixedCutContexts.context013, SevenLowerFixedCutContexts.context014, SevenLowerFixedCutContexts.context015, SevenLowerFixedCutContexts.context020, SevenLowerFixedCutContexts.context022, SevenLowerFixedCutContexts.context023, SevenLowerFixedCutContexts.context024, SevenLowerFixedCutContexts.context025, SevenLowerFixedCutContexts.context029, SevenLowerFixedCutContexts.context030, SevenLowerFixedCutContexts.context031]
def fuels : Fin 13 → ℕ := ![15, 15, 15, 15, 15, 11, 10, 10, 12, 13, 11, 11, 12]
def ids : Fin 13 → ℕ := ![2, 3, 4, 5, 115, 252, 352, 441, 475, 538, 589, 784, 819]

theorem cuts_checked : ∀ j : Fin 13,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup00
