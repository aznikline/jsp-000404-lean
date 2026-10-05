import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_516 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr0210a : m.d 0 2 + lam ≤ m.d 2 10)
    (htr0210b : m.d 0 2 < m.d 0 10)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd410a, hd410braw⟩ := m.hrange 4 10 (by decide)
  have hd410b : m.d 4 10 < 4*lam := by
    linarith only [hd410braw, hp]
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
    linarith only [hlam, htr0210b, htr024c, htr0410c])
  obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0210b, htr025c, htr0510c])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
    linarith only [hlam, htr024b, htr0410a, htr2410a])
  obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc4510xy, htr0210a, htr024a, htr2410c, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, htr025b, htr0510a, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, hd12a, hd34b, htr0210a, htr023a, htr123a, htr2410c, htr3410a])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd12a, hd410b, htr124a, htr245a, htr3410a, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  rcases m.htr 4 5 10 (by decide) (by decide) with
    ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
  ·
    linarith only [hlam, hd12a, hd510b, htr123a, htr234a, htr345a, htr4510a]
  ·
    linarith only [hlam, hd12a, hd45b, htr0210a, htr023a, htr123a, htr2510c, htr4510a]

theorem shard_516 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr0210a : m.d 0 2 + lam ≤ m.d 2 10)
    (htr0210b : m.d 0 2 < m.d 0 10)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_516 m htr023a htr024a htr024b htr024c htr025b htr025c htr0210a htr0210b htr123a htr124a htr234a

#print axioms shard_516
end Jsp404.NoSatElevenDBMTerminal
