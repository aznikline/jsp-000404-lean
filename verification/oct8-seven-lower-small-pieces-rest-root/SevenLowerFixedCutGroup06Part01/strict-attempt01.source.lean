import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup06Part01
open SevenLowerReplay
def contexts : Fin 14 → Context := ![SevenLowerFixedCutContexts.context209, SevenLowerFixedCutContexts.context210, SevenLowerFixedCutContexts.context211, SevenLowerFixedCutContexts.context212, SevenLowerFixedCutContexts.context213, SevenLowerFixedCutContexts.context214, SevenLowerFixedCutContexts.context215, SevenLowerFixedCutContexts.context216, SevenLowerFixedCutContexts.context217, SevenLowerFixedCutContexts.context218, SevenLowerFixedCutContexts.context219, SevenLowerFixedCutContexts.context221, SevenLowerFixedCutContexts.context222, SevenLowerFixedCutContexts.context230]
def fuels : Fin 14 → ℕ := ![19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 21, 21, 17]
def ids : Fin 14 → ℕ := ![4626, 4627, 4628, 4629, 4630, 4631, 4632, 4633, 4634, 4635, 4636, 4666, 4719, 4794]

theorem cuts_checked : ∀ j : Fin 14,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup06Part01
