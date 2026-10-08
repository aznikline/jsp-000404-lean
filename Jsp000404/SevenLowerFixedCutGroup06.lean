import Jsp000404.SevenLowerFixedCutGroup06Part00
import Jsp000404.SevenLowerFixedCutGroup06Part01
import Jsp000404.SevenLowerFixedCutGroup06Part02
import Jsp000404.SevenLowerFixedCutGroup06Part03
import Jsp000404.SevenLowerFixedCutGroup06Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup06
open SevenLowerReplay
def contexts : Fin 30 → Context := ![SevenLowerFixedCutContexts.context199, SevenLowerFixedCutContexts.context200, SevenLowerFixedCutContexts.context201, SevenLowerFixedCutContexts.context202, SevenLowerFixedCutContexts.context203, SevenLowerFixedCutContexts.context204, SevenLowerFixedCutContexts.context205, SevenLowerFixedCutContexts.context206, SevenLowerFixedCutContexts.context207, SevenLowerFixedCutContexts.context208, SevenLowerFixedCutContexts.context209, SevenLowerFixedCutContexts.context210, SevenLowerFixedCutContexts.context211, SevenLowerFixedCutContexts.context212, SevenLowerFixedCutContexts.context213, SevenLowerFixedCutContexts.context214, SevenLowerFixedCutContexts.context215, SevenLowerFixedCutContexts.context216, SevenLowerFixedCutContexts.context217, SevenLowerFixedCutContexts.context218, SevenLowerFixedCutContexts.context219, SevenLowerFixedCutContexts.context221, SevenLowerFixedCutContexts.context222, SevenLowerFixedCutContexts.context230, SevenLowerFixedCutContexts.context231, SevenLowerFixedCutContexts.context232, SevenLowerFixedCutContexts.context235, SevenLowerFixedCutContexts.context236, SevenLowerFixedCutContexts.context237, SevenLowerFixedCutContexts.context239]
def fuels : Fin 30 → ℕ := ![19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 21, 21, 17, 17, 18, 17, 17, 18, 19]
def ids : Fin 30 → ℕ := ![4534, 4535, 4536, 4537, 4538, 4539, 4540, 4541, 4581, 4604, 4626, 4627, 4628, 4629, 4630, 4631, 4632, 4633, 4634, 4635, 4636, 4666, 4719, 4794, 4852, 4891, 4945, 5026, 5145, 5197]

theorem cuts_checked : ∀ j : Fin 30,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 2
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 3
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 4
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 5
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 6
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 7
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 8
  · exact SevenLowerFixedCutGroup06Part00.cuts_checked 9
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 2
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 3
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 4
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 5
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 6
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 7
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 8
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 9
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 10
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 11
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 12
  · exact SevenLowerFixedCutGroup06Part01.cuts_checked 13
  · exact SevenLowerFixedCutGroup06Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup06Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup06Part02.cuts_checked 2
  · exact SevenLowerFixedCutGroup06Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup06Part04.cuts_checked 0
  · exact SevenLowerFixedCutGroup06Part04.cuts_checked 1

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup06
