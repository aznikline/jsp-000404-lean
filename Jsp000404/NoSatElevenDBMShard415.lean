import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_415 {lam p : ℝ} (m : ElevenModel lam p)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr2310a : m.d 2 3 + lam ≤ m.d 3 10)
    (htr2310b : m.d 2 3 < m.d 2 10)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, htr2310b, htr235c, htr2510c])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, htr2310b, htr236c, htr2610c])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, htr235b, htr2510a, htr3510a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc5610xy, htr2310a, htr235a, htr3510c, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, htr236b, htr2610a, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hd13a, hd45b, htr134a, htr2310a, htr234a, htr3510c, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd13a, hd510b, htr134a, htr345b, htr356a, htr4510a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 10 (by decide) (by decide) with
    ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
  ·
    linarith only [hlam, hd13a, hd610b, htr134a, htr345a, htr456a, htr5610a]
  ·
    linarith only [hlam, hd13a, hd56b, htr134a, htr2310a, htr234a, htr3610c, htr5610a]

theorem shard_415 {lam p : ℝ} (m : ElevenModel lam p)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr2310a : m.d 2 3 + lam ≤ m.d 3 10)
    (htr2310b : m.d 2 3 < m.d 2 10)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    : False :=
  proof_shard_415 m htr134a htr234a htr235a htr235b htr235c htr236b htr236c htr2310a htr2310b htr345a htr345b

#print axioms shard_415
end Jsp404.NoSatElevenDBMTerminal
