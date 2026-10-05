import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_086 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr1210a : m.d 1 2 + lam ≤ m.d 2 10)
    (htr1210b : m.d 1 2 < m.d 1 10)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd410a, hd410braw⟩ := m.hrange 4 10 (by decide)
  have hd410b : m.d 4 10 < 4*lam := by
    linarith only [hd410braw, hp]
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  have hforced1410 := (m.htr 1 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1410a, htr1410b, htr1410c, _, _⟩
    linarith only [hlam, htr1210b, htr124c, htr1410c])
  obtain ⟨htr1410a, htr1410b, htr1410c, _, _⟩ := hforced1410
  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
    linarith only [hlam, htr1210b, htr125c, htr1510c])
  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
  have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
    linarith only [hlam, htr124b, htr1410a, htr2410a])
  obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc4510xy, htr1210a, htr124a, htr2410c, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, htr125b, htr1510a, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, hc234yz, htr1210a, htr124a, htr2410c, htr3410a])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd02a, hd410b, htr024a, htr245a, htr3410a, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  rcases m.htr 4 5 10 (by decide) (by decide) with
    ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
  ·
    linarith only [hlam, hd02a, hd510b, htr023a, htr234a, htr345a, htr4510a]
  ·
    linarith only [hlam, hd02a, hd45b, htr023a, htr1210a, htr123a, htr2510c, htr4510a]

theorem shard_086 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr1210a : m.d 1 2 + lam ≤ m.d 2 10)
    (htr1210b : m.d 1 2 < m.d 1 10)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_086 m htr023a htr024a htr123a htr124a htr124b htr124c htr125b htr125c htr1210a htr1210b htr234a

#print axioms shard_086
end Jsp404.NoSatElevenDBMTerminal
