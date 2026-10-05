import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_188 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
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
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr039a, htr039b, htr039c, _, _⟩
    linarith only [hlam, htr013c, htr039a, htr139a])
  obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr035c, htr039b, htr059c])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr036c, htr039b, htr069c])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, htr035b, htr059a, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc569xy, htr013c, htr035a, htr139a, htr356a, htr359c])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, htr036b, htr069a, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hd23a, hd45b, htr134a, htr139a, htr234a, htr359c, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd23a, hd59b, htr234a, htr345b, htr356a, htr456a, htr459a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 9 (by decide) (by decide) with
    ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
  ·
    linarith only [hlam, hd23a, hd69b, htr234a, htr345a, htr456a, htr569a]
  ·
    linarith only [hlam, hd23a, hd56b, htr134a, htr139a, htr234a, htr369c, htr569a]

theorem shard_188 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    : False :=
  proof_shard_188 m htr013c htr035a htr035b htr035c htr036b htr036c htr134a htr139a htr234a htr345a htr345b

#print axioms shard_188
end Jsp404.NoSatElevenDBMTerminal
