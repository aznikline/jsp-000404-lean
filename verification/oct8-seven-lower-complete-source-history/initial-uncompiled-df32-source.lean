import Jsp000404.SevenLowerReplaySoundness
import Jsp000404.SevenLowerBranchRootCheck

set_option autoImplicit false
set_option pp.fullNames true

/-! SOURCE_ONLY final fixed-m6 lower-only provider.
The semantic checker has passed separately. The literal root-check producer
is undergoing its own validation; this source asserts no completed validation.
No caller supplies a word, context, order, profile, cycle library or Boolean
check. Row4 is free; neither HIGH nor a theta gauge is a hypothesis.
-/

namespace Jsp404.SevenLowerComplete

theorem complete (M : SatScalarModel.GenericModel 6 4)
    (hdef0 : SatScalarModel.rowDefect M 0 ≤ 2)
    (hdef1 : SatScalarModel.rowDefect M 1 ≤ 3)
    (hdef2 : SatScalarModel.rowDefect M 2 ≤ 3)
    (hdef3 : SatScalarModel.rowDefect M 3 ≤ 3)
    (hdef5 : SatScalarModel.rowDefect M 5 ≤ 3) : False :=
  SevenLowerReplaySoundness.checked_root_impossible
    SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles
    26 10813 SevenLowerBranchRootCheck.point_checked
    M hdef0 hdef1 hdef2 hdef3 hdef5

#print axioms complete

end Jsp404.SevenLowerComplete
