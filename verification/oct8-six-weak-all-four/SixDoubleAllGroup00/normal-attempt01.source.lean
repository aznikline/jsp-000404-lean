import Jsp000404.SixWeakAllGroup00Rows

/-! SOURCE_ONLY four-word typed-catalog pilot; not an all-direction closure. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixDoubleAllGroup00
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

theorem mask000_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixDoubleAllGroup00Data.Mask000.word)
    (hdef0 : SatScalarModel.rowDefect M 0 ≤ 2)
    (hdef2 : SatScalarModel.rowDefect M 2 ≤ 2)
    : False := by
  exact SixWeakOuterReplaySoundness.leafCheckB_sound M SixDoubleAllGroup00Data.Mask000.word hword SixDoubleAllGroup00Data.Mask000.rows
    (SixWeakAllGroup00Rows.rows_actual_mask000 M hword) hdef0 hdef2 SixDoubleAllGroup00Data.Mask000.library SixDoubleAllGroup00Data.Mask000.ids SixDoubleAllGroup00Data.Mask000.point_checked

#print axioms mask000_impossible

theorem mask202_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixDoubleAllGroup00Data.Mask202.word)
    (hdef0 : SatScalarModel.rowDefect M 0 ≤ 2)
    (hdef2 : SatScalarModel.rowDefect M 2 ≤ 2)
    : False := by
  exact SixWeakOuterReplaySoundness.leafCheckB_sound M SixDoubleAllGroup00Data.Mask202.word hword SixDoubleAllGroup00Data.Mask202.rows
    (SixWeakAllGroup00Rows.rows_actual_mask202 M hword) hdef0 hdef2 SixDoubleAllGroup00Data.Mask202.library SixDoubleAllGroup00Data.Mask202.ids SixDoubleAllGroup00Data.Mask202.point_checked

#print axioms mask202_impossible

theorem mask472_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixDoubleAllGroup00Data.Mask472.word)
    (hdef0 : SatScalarModel.rowDefect M 0 ≤ 2)
    (hdef2 : SatScalarModel.rowDefect M 2 ≤ 2)
    : False := by
  exact SixWeakOuterReplaySoundness.leafCheckB_sound M SixDoubleAllGroup00Data.Mask472.word hword SixDoubleAllGroup00Data.Mask472.rows
    (SixWeakAllGroup00Rows.rows_actual_mask472 M hword) hdef0 hdef2 SixDoubleAllGroup00Data.Mask472.library SixDoubleAllGroup00Data.Mask472.ids SixDoubleAllGroup00Data.Mask472.point_checked

#print axioms mask472_impossible

theorem mask1023_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixDoubleAllGroup00Data.Mask1023.word)
    (hdef0 : SatScalarModel.rowDefect M 0 ≤ 2)
    (hdef2 : SatScalarModel.rowDefect M 2 ≤ 2)
    : False := by
  exact SixWeakOuterReplaySoundness.leafCheckB_sound M SixDoubleAllGroup00Data.Mask1023.word hword SixDoubleAllGroup00Data.Mask1023.rows
    (SixWeakAllGroup00Rows.rows_actual_mask1023 M hword) hdef0 hdef2 SixDoubleAllGroup00Data.Mask1023.library SixDoubleAllGroup00Data.Mask1023.ids SixDoubleAllGroup00Data.Mask1023.point_checked

#print axioms mask1023_impossible

theorem group_impossible (M : GenericModel 5 4) (j : Fin 4)
    (hword : WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (SixWeakAllGroup00Rows.catalogIndices j))))
    (hdef0 : SatScalarModel.rowDefect M 0 ≤ 2)
    (hdef2 : SatScalarModel.rowDefect M 2 ≤ 2)
    : False := by
  fin_cases j
  · change WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (0 : Fin 62))) at hword
    rw [← SixDoubleAllGroup00Data.Mask000.word_catalog] at hword
    exact mask000_impossible M hword hdef0 hdef2
  · change WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (17 : Fin 62))) at hword
    rw [← SixDoubleAllGroup00Data.Mask202.word_catalog] at hword
    exact mask202_impossible M hword hdef0 hdef2
  · change WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (26 : Fin 62))) at hword
    rw [← SixDoubleAllGroup00Data.Mask472.word_catalog] at hword
    exact mask472_impossible M hword hdef0 hdef2
  · change WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (61 : Fin 62))) at hword
    rw [← SixDoubleAllGroup00Data.Mask1023.word_catalog] at hword
    exact mask1023_impossible M hword hdef0 hdef2

#print axioms group_impossible
end Jsp404.SixDoubleAllGroup00
