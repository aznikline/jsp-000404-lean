import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_464 {lam p : ℝ} (m : ElevenModel lam p)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr1310a : m.d 3 10 + lam ≤ m.d 1 3)
    (htr1310c : m.d 1 10 < m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd510a := (m.hrange 5 10 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
    linarith only [hlam, htr1310c, htr135b, htr1510b])
  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
  have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
    linarith only [hlam, htr1310c, htr136b, htr1610b])
  obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, htr135c, htr1510a, htr3510a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc5610yx, htr1310a, htr135a, htr3510b, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, htr136c, htr1610a, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hd23b, hd45a, htr1310a, htr134a, htr234a, htr3510b, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd23b, hd510a, htr234a, htr345c, htr356a, htr4510a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 10 (by decide) (by decide) with
    ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
  ·
    linarith only [hlam, hd23b, hd56a, htr1310a, htr134a, htr234a, htr3610b, htr5610a]
  ·
    linarith only [hlam, hd23b, hd610a, htr234a, htr345a, htr456a, htr5610a]

theorem shard_464 {lam p : ℝ} (m : ElevenModel lam p)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr1310a : m.d 3 10 + lam ≤ m.d 1 3)
    (htr1310c : m.d 1 10 < m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    : False :=
  proof_shard_464 m htr134a htr135a htr135b htr135c htr136b htr136c htr1310a htr1310c htr234a htr345a htr345c

#print axioms shard_464
end Jsp404.NoSatElevenDBMTerminal
