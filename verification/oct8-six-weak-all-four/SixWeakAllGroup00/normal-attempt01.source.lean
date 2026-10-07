import Jsp000404.SixWeakAllGroup00Rows

/-! SOURCE_ONLY four-word typed-catalog pilot; not an all-direction closure. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixWeakAllGroup00
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

theorem mask000_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup00Data.Mask000.word)
    (hdef1 : SatScalarModel.rowDefect M 1 ≤ 2)
    (hdef3 : SatScalarModel.rowDefect M 3 ≤ 3)
    : False := by
  exact SixWeakOuterReplaySoundness.leafCheckA_sound M SixWeakAllGroup00Data.Mask000.word hword SixWeakAllGroup00Data.Mask000.rows
    (SixWeakAllGroup00Rows.rows_actual_mask000 M hword) hdef1 hdef3 SixWeakAllGroup00Data.Mask000.library SixWeakAllGroup00Data.Mask000.ids SixWeakAllGroup00Data.Mask000.point_checked

#print axioms mask000_impossible

theorem mask202_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup00Data.Mask202.word)
    (hdef1 : SatScalarModel.rowDefect M 1 ≤ 2)
    (hdef3 : SatScalarModel.rowDefect M 3 ≤ 3)
    : False := by
  exact SixWeakOuterReplaySoundness.leafCheckA_sound M SixWeakAllGroup00Data.Mask202.word hword SixWeakAllGroup00Data.Mask202.rows
    (SixWeakAllGroup00Rows.rows_actual_mask202 M hword) hdef1 hdef3 SixWeakAllGroup00Data.Mask202.library SixWeakAllGroup00Data.Mask202.ids SixWeakAllGroup00Data.Mask202.point_checked

#print axioms mask202_impossible

theorem mask472_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup00Data.Mask472.word)
    (hdef1 : SatScalarModel.rowDefect M 1 ≤ 2)
    (hdef3 : SatScalarModel.rowDefect M 3 ≤ 3)
    : False := by
  exact SixWeakOuterReplaySoundness.leafCheckA_sound M SixWeakAllGroup00Data.Mask472.word hword SixWeakAllGroup00Data.Mask472.rows
    (SixWeakAllGroup00Rows.rows_actual_mask472 M hword) hdef1 hdef3 SixWeakAllGroup00Data.Mask472.library SixWeakAllGroup00Data.Mask472.ids SixWeakAllGroup00Data.Mask472.point_checked

#print axioms mask472_impossible

theorem mask1023_impossible (M : GenericModel 5 4)
    (hword : WordSound M SixWeakAllGroup00Data.Mask1023.word)
    (hdef1 : SatScalarModel.rowDefect M 1 ≤ 2)
    (hdef3 : SatScalarModel.rowDefect M 3 ≤ 3)
    : False := by
  exact SixWeakOuterReplaySoundness.leafCheckA_sound M SixWeakAllGroup00Data.Mask1023.word hword SixWeakAllGroup00Data.Mask1023.rows
    (SixWeakAllGroup00Rows.rows_actual_mask1023 M hword) hdef1 hdef3 SixWeakAllGroup00Data.Mask1023.library SixWeakAllGroup00Data.Mask1023.ids SixWeakAllGroup00Data.Mask1023.point_checked

#print axioms mask1023_impossible

theorem group_impossible (M : GenericModel 5 4) (j : Fin 4)
    (hword : WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (SixWeakAllGroup00Rows.catalogIndices j))))
    (hdef1 : SatScalarModel.rowDefect M 1 ≤ 2)
    (hdef3 : SatScalarModel.rowDefect M 3 ≤ 3)
    : False := by
  fin_cases j
  · change WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (0 : Fin 62))) at hword
    rw [← SixWeakAllGroup00Data.Mask000.word_catalog] at hword
    exact mask000_impossible M hword hdef1 hdef3
  · change WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (17 : Fin 62))) at hword
    rw [← SixWeakAllGroup00Data.Mask202.word_catalog] at hword
    exact mask202_impossible M hword hdef1 hdef3
  · change WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (26 : Fin 62))) at hword
    rw [← SixWeakAllGroup00Data.Mask472.word_catalog] at hword
    exact mask472_impossible M hword hdef1 hdef3
  · change WordSound M (SixOuterWordCatalogComplete.wordOfMask
      (SixOuterWordCatalogComplete.catalog (61 : Fin 62))) at hword
    rw [← SixWeakAllGroup00Data.Mask1023.word_catalog] at hword
    exact mask1023_impossible M hword hdef1 hdef3

#print axioms group_impossible
end Jsp404.SixWeakAllGroup00
