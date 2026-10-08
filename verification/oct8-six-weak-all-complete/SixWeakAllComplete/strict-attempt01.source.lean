import Jsp000404.SixWeakAllGroup00
import Jsp000404.SixWeakAllGroup01
import Jsp000404.SixWeakAllGroup02
import Jsp000404.SixWeakAllGroup03
import Jsp000404.SixWeakAllGroup04
import Jsp000404.SixWeakAllCatalogCover

/-! SOURCE_ONLY all62 no-word interface. Every group and this terminal still needs independent kernel acceptance. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixWeakAllComplete
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

theorem complete (M : GenericModel 5 4)
    (hdef1 : SatScalarModel.rowDefect M 1 ≤ 2)
    (hdef3 : SatScalarModel.rowDefect M 3 ≤ 3)
    : False := by
  obtain ⟨c, hword⟩ := SixOuterWordCatalogComplete.exists_catalog_model_word M
  rcases SixWeakAllCatalogCover.catalog_index_cover c with
    ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [← hj] at hword
    exact SixWeakAllGroup00.group_impossible M j hword hdef1 hdef3
  · rw [← hj] at hword
    exact SixWeakAllGroup01.group_impossible M j hword hdef1 hdef3
  · rw [← hj] at hword
    exact SixWeakAllGroup02.group_impossible M j hword hdef1 hdef3
  · rw [← hj] at hword
    exact SixWeakAllGroup03.group_impossible M j hword hdef1 hdef3
  · rw [← hj] at hword
    exact SixWeakAllGroup04.group_impossible M j hword hdef1 hdef3

#print axioms complete
end Jsp404.SixWeakAllComplete
