import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_434 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr1310a : m.d 3 10 + lam ≤ m.d 1 3)
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
  have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
    linarith only [hlam, htr013b, htr0310a, htr1310a])
  obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0310c, htr035b, htr0510b])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0310c, htr036b, htr0610b])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, htr035c, htr0510a, htr3510a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc5610yx, htr013b, htr035a, htr1310a, htr3510b, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, htr036c, htr0610a, htr3610a])
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

theorem shard_434 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr1310a : m.d 3 10 + lam ≤ m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    : False :=
  proof_shard_434 m htr013b htr035a htr035b htr035c htr036b htr036c htr134a htr1310a htr234a htr345a htr345c

#print axioms shard_434
end Jsp404.NoSatElevenDBMTerminal
