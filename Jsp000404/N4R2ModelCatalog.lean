import Jsp000404.N4R2ModelWordSoundness
import Jsp000404.N4R2WordCatalogComplete

/-! The finite catalog membership consequence for actual model directions.
This final bridge is separate from the generic row semantics, so the latter
does not depend on replaying the complete catalog proof.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2ModelCatalog

open SatScalarModel N4R2ModelWordSoundness

/-- Actual model fields internally choose a direction word; packet coverage
then identifies its catalog entry without a caller orientation premise. -/
theorem exists_catalog_model_word (M : GenericModel 7 4) :
    ∃ id : Fin 24698, WordSound M (N4R2WordTree.catalog id) := by
  obtain ⟨w, hw⟩ := exists_model_word M
  obtain ⟨id, he⟩ := N4R2WordTree.catalog_complete w (wordSound_packetValid M w hw)
  exact ⟨id, he ▸ hw⟩

#print axioms exists_catalog_model_word

end Jsp404.N4R2ModelCatalog
