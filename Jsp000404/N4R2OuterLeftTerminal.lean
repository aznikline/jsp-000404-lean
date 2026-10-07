import Jsp000404.N4R2OuterLeftAllChecked
import Jsp000404.N4R2ModelCatalog
import Jsp000404.N4R2OuterLeftReplaySoundness

/-! Caller-free outer-left terminal, prepared as SOURCE_ONLY.

The actual model supplies its own triangle word and catalog index. The
new exhaustive data module must supply every checked leaf. This source
is not a verified terminal until the entire new catalog dependency chain
and this module have strict and genuine normal verification receipts.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2OuterLeftTerminal

open SatScalarModel

/-- Only original scalar row 1 has defect two; original rows 2..6 have
defect four. Row 0 is unrestricted. No word, catalog index, accepted
certificate, HIGH premise, or additional delta bound is a caller input. -/
theorem outer_left_low1_pure_tail_impossible (M : GenericModel 7 4)
    (hdef1 : SatScalarModel.rowDefect M 1 = 2)
    (htails : ∀ i : Fin 7, 1 < i.val → SatScalarModel.rowDefect M i = 4) : False := by
  obtain ⟨id, hword⟩ := N4R2ModelCatalog.exists_catalog_model_word M
  exact N4R2OuterLeftReplaySoundness.leafCheck_sound
    (N4R2OuterLeftData.libraryFor id) M (N4R2WordTree.catalog id) hword hdef1 htails
    (N4R2OuterLeftData.leafData id) (N4R2OuterLeftData.all_leaves_checked id)

#print axioms outer_left_low1_pure_tail_impossible

end Jsp404.N4R2OuterLeftTerminal
