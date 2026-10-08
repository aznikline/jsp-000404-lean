import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY exact smaller fixed-cut proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup06Part00
open SevenLowerReplay
def contexts : Fin 10 → Context := ![SevenLowerFixedCutContexts.context199, SevenLowerFixedCutContexts.context200, SevenLowerFixedCutContexts.context201, SevenLowerFixedCutContexts.context202, SevenLowerFixedCutContexts.context203, SevenLowerFixedCutContexts.context204, SevenLowerFixedCutContexts.context205, SevenLowerFixedCutContexts.context206, SevenLowerFixedCutContexts.context207, SevenLowerFixedCutContexts.context208]
def fuels : Fin 10 → ℕ := ![19, 19, 19, 19, 19, 19, 19, 19, 19, 19]
def ids : Fin 10 → ℕ := ![4534, 4535, 4536, 4537, 4538, 4539, 4540, 4541, 4581, 4604]

theorem cuts_checked : ∀ j : Fin 10,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by decide

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup06Part00
