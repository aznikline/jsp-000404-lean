import Jsp000404.SixWeakAllGroup00Rows
import Jsp000404.SixWeakAllGroup01Rows
import Jsp000404.SixWeakAllGroup02Rows
import Jsp000404.SixWeakAllGroup03Rows
import Jsp000404.SixWeakAllGroup04Rows

/-! SOURCE_ONLY until all group dependencies and this exact finite coverage proof pass kernel checks. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixWeakAllCatalogCover

theorem catalog_index_cover (c : Fin 62) :
    (∃ j : Fin 4, SixWeakAllGroup00Rows.catalogIndices j = c) ∨
    (∃ j : Fin 16, SixWeakAllGroup01Rows.catalogIndices j = c) ∨
    (∃ j : Fin 16, SixWeakAllGroup02Rows.catalogIndices j = c) ∨
    (∃ j : Fin 16, SixWeakAllGroup03Rows.catalogIndices j = c) ∨
    (∃ j : Fin 10, SixWeakAllGroup04Rows.catalogIndices j = c) := by
  fin_cases c
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inr (Or.inl ⟨0, rfl⟩)
  · exact Or.inr (Or.inl ⟨1, rfl⟩)
  · exact Or.inr (Or.inl ⟨2, rfl⟩)
  · exact Or.inr (Or.inl ⟨3, rfl⟩)
  · exact Or.inr (Or.inl ⟨4, rfl⟩)
  · exact Or.inr (Or.inl ⟨5, rfl⟩)
  · exact Or.inr (Or.inl ⟨6, rfl⟩)
  · exact Or.inr (Or.inl ⟨7, rfl⟩)
  · exact Or.inr (Or.inl ⟨8, rfl⟩)
  · exact Or.inr (Or.inl ⟨9, rfl⟩)
  · exact Or.inr (Or.inl ⟨10, rfl⟩)
  · exact Or.inr (Or.inl ⟨11, rfl⟩)
  · exact Or.inr (Or.inl ⟨12, rfl⟩)
  · exact Or.inr (Or.inl ⟨13, rfl⟩)
  · exact Or.inr (Or.inl ⟨14, rfl⟩)
  · exact Or.inr (Or.inl ⟨15, rfl⟩)
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨0, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨1, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨2, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨4, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨6, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨7, rfl⟩))
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨8, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨9, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨10, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨11, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨12, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨13, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨14, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨15, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨0, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨1, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨2, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨3, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨4, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨5, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨6, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨7, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨8, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨9, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨10, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨11, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨12, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨13, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨14, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨15, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨0, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨1, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨2, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨3, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨4, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨5, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨6, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨7, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨8, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨9, rfl⟩))))
  · exact Or.inl ⟨3, rfl⟩

#print axioms catalog_index_cover
end Jsp404.SixWeakAllCatalogCover
