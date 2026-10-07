import Jsp000404.N4R2AllLeavesChecked
import Jsp000404.N4R2ModelCatalog
import Jsp000404.N4R2RowDataReplaySoundness

/-!
# Complete n4 R2 between-model terminal

The model internally supplies its 35 triangle directions, the finite packet
tree supplies a catalog entry, and the concrete checked leaf library supplies
the contradiction. No caller word, catalog membership, row order, accepted DBM
row, or goal bound is a premise.

This source is not a completion claim until all concrete catalog/leaf modules
and this terminal have genuine strict and normal receipts. The profile is the
n4 between R2 profile; no original all-n or prize theorem is asserted.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2BetweenTerminal

open SatScalarModel

theorem between_pure_tail_impossible (M : GenericModel 7 4)
    (hdef0 : SatScalarModel.rowDefect M 0 = 2)
    (hdef6 : SatScalarModel.rowDefect M 6 = 2)
    (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → SatScalarModel.rowDefect M i = 4) :
    False := by
  obtain ⟨id, hword⟩ := N4R2ModelCatalog.exists_catalog_model_word M
  exact N4R2RowDataReplaySoundness.leafCheck_sound (N4R2ReplayData.libraryFor id) M
    (N4R2WordTree.catalog id) hword hdef0 hdef6 htails
    (N4R2ReplayData.leafData id) (N4R2ReplayData.all_leaves_checked id)

#print axioms between_pure_tail_impossible

end Jsp404.N4R2BetweenTerminal
