import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_617 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr1310a : m.d 1 3 + lam ≤ m.d 3 10)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd23a := (m.hrange 2 3 (by decide)).1
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
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
    linarith only [hlam, hc023zy, htr0310a, htr1310a, htr134a, htr234a])
  obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
  have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
    linarith only [hlam, htr0310b, htr034c, htr0410c])
  obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0310b, htr035c, htr0510c])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0310b, htr036c, htr0610c])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, htr014b, htr0410a, htr134b, htr3410a])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc4510xy, htr013b, htr0310a, htr134a, htr3410c, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, htr015b, htr0510a, htr135b, htr3510a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc5610xy, htr013b, htr0310a, htr135a, htr3510c, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, htr016b, htr0610a, htr136b, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hd23a, hd45b, htr1310a, htr134a, htr234a, htr3510c, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd23a, hd510b, htr235a, htr356a, htr4510a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 10 (by decide) (by decide) with
    ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
  ·
    linarith only [hlam, hd23a, hd610b, htr234a, htr345a, htr456a, htr5610a]
  ·
    linarith only [hlam, hd23a, hd56b, htr1310a, htr134a, htr234a, htr3610c, htr5610a]

theorem shard_617 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr1310a : m.d 1 3 + lam ≤ m.d 3 10)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    : False :=
  proof_shard_617 m htr013b htr014b htr015b htr016b htr034c htr035c htr036c htr134a htr134b htr135a htr135b htr136b htr1310a htr234a htr235a

#print axioms shard_617
end Jsp404.NoSatElevenDBMTerminal
