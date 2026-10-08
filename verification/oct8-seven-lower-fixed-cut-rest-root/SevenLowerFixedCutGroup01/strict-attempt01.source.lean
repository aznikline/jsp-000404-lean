import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup01
open SevenLowerReplay
def contexts : Fin 19 → Context := ![SevenLowerFixedCutContexts.context032, SevenLowerFixedCutContexts.context033, SevenLowerFixedCutContexts.context034, SevenLowerFixedCutContexts.context035, SevenLowerFixedCutContexts.context036, SevenLowerFixedCutContexts.context037, SevenLowerFixedCutContexts.context038, SevenLowerFixedCutContexts.context039, SevenLowerFixedCutContexts.context040, SevenLowerFixedCutContexts.context041, SevenLowerFixedCutContexts.context042, SevenLowerFixedCutContexts.context043, SevenLowerFixedCutContexts.context044, SevenLowerFixedCutContexts.context045, SevenLowerFixedCutContexts.context046, SevenLowerFixedCutContexts.context047, SevenLowerFixedCutContexts.context048, SevenLowerFixedCutContexts.context049, SevenLowerFixedCutContexts.context052]
def fuels : Fin 19 → ℕ := ![13, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 17, 16]
def ids : Fin 19 → ℕ := ![999, 1002, 1003, 1004, 1041, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1332, 1412, 1531]

theorem cuts_checked : ∀ j : Fin 19,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup01
