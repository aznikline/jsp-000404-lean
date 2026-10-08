import Jsp000404.SevenLowerFixedCutGroup02Part00
import Jsp000404.SevenLowerFixedCutGroup02Part01
import Jsp000404.SevenLowerFixedCutGroup02Part02
import Jsp000404.SevenLowerFixedCutGroup02Part03
import Jsp000404.SevenLowerFixedCutGroup02Part04
import Mathlib.Tactic.FinCases
import Jsp000404.SevenLowerFixedCutContexts

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutGroup02
open SevenLowerReplay
def contexts : Fin 28 → Context := ![SevenLowerFixedCutContexts.context053, SevenLowerFixedCutContexts.context055, SevenLowerFixedCutContexts.context056, SevenLowerFixedCutContexts.context057, SevenLowerFixedCutContexts.context058, SevenLowerFixedCutContexts.context059, SevenLowerFixedCutContexts.context060, SevenLowerFixedCutContexts.context061, SevenLowerFixedCutContexts.context062, SevenLowerFixedCutContexts.context063, SevenLowerFixedCutContexts.context064, SevenLowerFixedCutContexts.context065, SevenLowerFixedCutContexts.context066, SevenLowerFixedCutContexts.context067, SevenLowerFixedCutContexts.context068, SevenLowerFixedCutContexts.context069, SevenLowerFixedCutContexts.context070, SevenLowerFixedCutContexts.context071, SevenLowerFixedCutContexts.context072, SevenLowerFixedCutContexts.context073, SevenLowerFixedCutContexts.context074, SevenLowerFixedCutContexts.context075, SevenLowerFixedCutContexts.context077, SevenLowerFixedCutContexts.context078, SevenLowerFixedCutContexts.context082, SevenLowerFixedCutContexts.context083, SevenLowerFixedCutContexts.context084, SevenLowerFixedCutContexts.context085]
def fuels : Fin 28 → ℕ := ![16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 18, 18, 17, 17, 18, 19]
def ids : Fin 28 → ℕ := ![1669, 1673, 1674, 1738, 1739, 1740, 1741, 1742, 1783, 1808, 1809, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1930, 2003, 2072, 2150, 2212, 2248]

theorem cuts_checked : ∀ j : Fin 28,
    check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles (fuels j) (contexts j) (ids j) = true := by
  intro j
  fin_cases j
  · exact SevenLowerFixedCutGroup02Part00.cuts_checked 0
  · exact SevenLowerFixedCutGroup02Part00.cuts_checked 1
  · exact SevenLowerFixedCutGroup02Part00.cuts_checked 2
  · exact SevenLowerFixedCutGroup02Part01.cuts_checked 0
  · exact SevenLowerFixedCutGroup02Part01.cuts_checked 1
  · exact SevenLowerFixedCutGroup02Part01.cuts_checked 2
  · exact SevenLowerFixedCutGroup02Part01.cuts_checked 3
  · exact SevenLowerFixedCutGroup02Part01.cuts_checked 4
  · exact SevenLowerFixedCutGroup02Part01.cuts_checked 5
  · exact SevenLowerFixedCutGroup02Part01.cuts_checked 6
  · exact SevenLowerFixedCutGroup02Part01.cuts_checked 7
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 0
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 1
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 2
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 3
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 4
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 5
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 6
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 7
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 8
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 9
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 10
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 11
  · exact SevenLowerFixedCutGroup02Part02.cuts_checked 12
  · exact SevenLowerFixedCutGroup02Part03.cuts_checked 0
  · exact SevenLowerFixedCutGroup02Part03.cuts_checked 1
  · exact SevenLowerFixedCutGroup02Part03.cuts_checked 2
  · exact SevenLowerFixedCutGroup02Part04.cuts_checked 0

#print axioms cuts_checked
end Jsp404.SevenLowerFixedCutGroup02
