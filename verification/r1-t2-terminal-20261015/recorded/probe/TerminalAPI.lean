import Jsp000404.R1DispatchT2

namespace Jsp404

def ExpectedTerminal : Prop :=
  ∀ (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin 7 → Plane₂} (hleg : Section4Legality c lam)
    {v a : Fin 7} (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (htail : ∀ w : Fin 7, w ≠ v → w ≠ a →
      3 ≤ rowDefect 4 lam (directionRow o e c w))
    (hF : potential lam (directionRows o e c) = 21), False

example : ExpectedTerminal := @r1_seven_phi21_terminal

end Jsp404

#print axioms Jsp404.r1_seven_phi21_terminal
#print axioms Jsp404.r1_phi21_unique_defect4
