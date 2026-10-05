import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_537 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    (htr1210c : m.d 1 10 < m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd410a := (m.hrange 4 10 (by decide)).1
  have hd510a := (m.hrange 5 10 (by decide)).1
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  have hforced1410 := (m.htr 1 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1410a, htr1410b, htr1410c, _, _⟩
    linarith only [hlam, htr1210c, htr124b, htr1410b])
  obtain ⟨htr1410a, htr1410b, htr1410c, _, _⟩ := hforced1410
  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
    linarith only [hlam, htr1210c, htr125b, htr1510b])
  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
  have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
    linarith only [hlam, htr124c, htr1410a, htr2410a])
  obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc4510yx, htr1210a, htr124a, htr2410b, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, htr125c, htr1510a, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, hc234zy, htr1210a, htr124a, htr2410b, htr3410a])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd02b, hd410a, htr024a, htr245a, htr3410a, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  rcases m.htr 4 5 10 (by decide) (by decide) with
    ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
  ·
    linarith only [hlam, hd02b, hd45a, htr023a, htr1210a, htr123a, htr2510b, htr4510a]
  ·
    linarith only [hlam, hd02b, hd510a, htr023a, htr234a, htr345a, htr4510a]

theorem shard_537 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr1210a : m.d 2 10 + lam ≤ m.d 1 2)
    (htr1210c : m.d 1 10 < m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_537 m htr023a htr024a htr123a htr124a htr124b htr124c htr125b htr125c htr1210a htr1210c htr234a

#print axioms shard_537
end Jsp404.NoSatElevenDBMTerminal
