import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup01Part01
open SevenLowerReplay
def contexts : Fin 12 → Context := ![SevenLowerFixedCutContexts.context036, SevenLowerFixedCutContexts.context037, SevenLowerFixedCutContexts.context038, SevenLowerFixedCutContexts.context039, SevenLowerFixedCutContexts.context040, SevenLowerFixedCutContexts.context041, SevenLowerFixedCutContexts.context042, SevenLowerFixedCutContexts.context043, SevenLowerFixedCutContexts.context044, SevenLowerFixedCutContexts.context045, SevenLowerFixedCutContexts.context046, SevenLowerFixedCutContexts.context047]
def fuels : Fin 12 → ℕ := ![15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15]
def ids : Fin 12 → ℕ := ![1041, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154]

theorem cuts_checked : ∀ j : Fin 12,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup01Part01
