import Jsp000404.SixDoubleAllGroup00
import Jsp000404.SixDoubleAllGroup01
import Jsp000404.SixDoubleAllGroup02
import Jsp000404.SixDoubleAllGroup03
import Jsp000404.SixDoubleAllGroup04
import Jsp000404.SixWeakAllCatalogCover

/-! SOURCE_ONLY all62 no-word interface. Every group and this terminal still needs independent kernel acceptance. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixDoubleAllComplete
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

theorem complete (M : GenericModel 5 4)
    (hdef0 : SatScalarModel.rowDefect M 0 ≤ 2)
    (hdef2 : SatScalarModel.rowDefect M 2 ≤ 2)
    : False := by
  obtain ⟨c, hword⟩ := SixOuterWordCatalogComplete.exists_catalog_model_word M
  rcases SixWeakAllCatalogCover.catalog_index_cover c with
    ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [← hj] at hword
    exact SixDoubleAllGroup00.group_impossible M j hword hdef0 hdef2
  · rw [← hj] at hword
    exact SixDoubleAllGroup01.group_impossible M j hword hdef0 hdef2
  · rw [← hj] at hword
    exact SixDoubleAllGroup02.group_impossible M j hword hdef0 hdef2
  · rw [← hj] at hword
    exact SixDoubleAllGroup03.group_impossible M j hword hdef0 hdef2
  · rw [← hj] at hword
    exact SixDoubleAllGroup04.group_impossible M j hword hdef0 hdef2

#print axioms complete
end Jsp404.SixDoubleAllComplete
