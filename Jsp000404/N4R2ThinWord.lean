import Jsp000404.N4R2WordDefinitions
import Mathlib.Data.List.OfFn
import Init.Data.List.Sort.Lemmas
import Init.Data.List.FinRange
import Init.Data.List.Erase

/-!
# Pure finite word-to-row computation

This module uses only finite labels, Boolean comparisons, and list sorting.
Its row algorithm is the same as the frozen actual-model semantic bridge.
Large finite replay data can import it without importing real geometry.
-/

set_option autoImplicit false

namespace Jsp404.N4R2ThinWord

abbrev Word := N4R2WordDefinitions.Word
abbrev triples := N4R2WordDefinitions.triples
abbrev tripleIndex := N4R2WordDefinitions.tripleIndex

/-- The same diagonal sentinel and triangle-bit comparator as the actual
model bridge.  The diagonal is erased before any row is sorted. -/
def rowCompare (w : Word) (i u v : Fin 7) : Bool :=
  if u = v then true else if u = i then true else if v = i then false
  else if u < v then !(w (tripleIndex i u v)) else w (tripleIndex i v u)

/-- All six distinct neighbor labels, sorted using only the direction word. -/
def sortedNeighbors (w : Word) (i : Fin 7) : List (Fin 7) :=
  ((List.finRange 7).erase i).mergeSort (rowCompare w i)

abbrev rowLabels := sortedNeighbors

theorem sortedNeighbors_perm (w : Word) (i : Fin 7) :
    (sortedNeighbors w i).Perm ((List.finRange 7).erase i) :=
  List.mergeSort_perm _ _

theorem rowLabels_perm (w : Word) (i : Fin 7) :
    (rowLabels w i).Perm ((List.finRange 7).erase i) :=
  sortedNeighbors_perm w i

theorem rowLabels_length (w : Word) (i : Fin 7) : (rowLabels w i).length = 6 := by
  have hl := (rowLabels_perm w i).length_eq
  simpa only [List.length_erase_of_mem (List.mem_finRange i), List.length_finRange] using hl

theorem sortedNeighbors_length (w : Word) (i : Fin 7) :
    (sortedNeighbors w i).length = 6 := rowLabels_length w i

/-- Computable complete six-label order determined solely by the word. -/
def rows (w : Word) (i : Fin 7) (k : Fin 6) : Fin 7 :=
  (rowLabels w i).get (Fin.cast (rowLabels_length w i).symm k)

theorem ofFn_rows (w : Word) (i : Fin 7) : List.ofFn (rows w i) = rowLabels w i := by
  have h := List.ofFn_congr (rowLabels_length w i) (rowLabels w i).get
  exact h.symm.trans (List.ofFn_get (rowLabels w i))

#print axioms sortedNeighbors_perm
#print axioms rowLabels_length
#print axioms ofFn_rows

end Jsp404.N4R2ThinWord
