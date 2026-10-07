import Jsp000404.N4R2ThinWord
import Jsp000404.N4R2ModelWordSoundness

/-! The pure word computation is definitionally the frozen model computation.
Proof irrelevance identifies the length witnesses used to index six labels.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2ThinWordSoundness

theorem rowCompare_eq (w : N4R2ThinWord.Word) (i : Fin 7) :
    N4R2ThinWord.rowCompare w i = N4R2ModelWordSoundness.rowCompare w i := rfl

theorem sortedNeighbors_eq (w : N4R2ThinWord.Word) (i : Fin 7) :
    N4R2ThinWord.sortedNeighbors w i = N4R2ModelWordSoundness.rowLabels w i := rfl

theorem rowLabels_eq (w : N4R2ThinWord.Word) (i : Fin 7) :
    N4R2ThinWord.rowLabels w i = N4R2ModelWordSoundness.rowLabels w i := rfl

theorem rows_eq (w : N4R2ThinWord.Word) (i : Fin 7) :
    N4R2ThinWord.rows w i = N4R2ModelWordSoundness.rows w i := rfl

#print axioms rowCompare_eq
#print axioms sortedNeighbors_eq
#print axioms rowLabels_eq
#print axioms rows_eq

end Jsp404.N4R2ThinWordSoundness
