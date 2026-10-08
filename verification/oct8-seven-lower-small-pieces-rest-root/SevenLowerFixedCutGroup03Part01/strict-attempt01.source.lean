import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup03Part01
open SevenLowerReplay
def contexts : Fin 10 → Context := ![SevenLowerFixedCutContexts.context093, SevenLowerFixedCutContexts.context096, SevenLowerFixedCutContexts.context098, SevenLowerFixedCutContexts.context099, SevenLowerFixedCutContexts.context100, SevenLowerFixedCutContexts.context101, SevenLowerFixedCutContexts.context102, SevenLowerFixedCutContexts.context103, SevenLowerFixedCutContexts.context104, SevenLowerFixedCutContexts.context105]
def fuels : Fin 10 → ℕ := ![17, 16, 15, 15, 15, 15, 15, 15, 15, 15]
def ids : Fin 10 → ℕ := ![2515, 2619, 2623, 2624, 2625, 2626, 2627, 2628, 2629, 2630]

theorem cuts_checked : ∀ j : Fin 10,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup03Part01
