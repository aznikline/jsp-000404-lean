import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_521 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr239a : m.d 3 9 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc349xy, hc349yx, hc349yz, hc349zy⟩ := endpoint_caps m 3 4 9 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc359xy, hc359yx, hc359yz, hc359zy⟩ := endpoint_caps m 3 5 9 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr039a, htr039b, htr039c, _, _⟩
    linarith only [hlam, htr023b, htr039a, htr239a])
  obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
    linarith only [hlam, htr034b, htr039c, htr049b])
  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr035b, htr039c, htr059b])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr036b, htr039c, htr069b])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr139a, htr139b, htr139c, _, _⟩
    linarith only [hlam, hc012zy, htr023a, htr123b, htr139a, htr239a])
  obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, htr034c, htr049a, htr349a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc459yx, htr023b, htr034a, htr239a, htr345a, htr349b])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc349yx, htr134b, htr139a, htr145a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, htr035c, htr059a, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc569yx, htr023b, htr035a, htr239a, htr356a, htr359b])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc359yx, htr135b, htr139a, htr156a, htr356a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, htr036c, htr069a, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc345zy, htr235a, htr239a, htr359b, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd01b, hd59a, htr015a, htr156a, htr456a, htr459a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 9 (by decide) (by decide) with
    ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
  ·
    linarith only [hlam, hc356zy, htr236a, htr239a, htr369b, htr569a]
  ·
    linarith only [hlam, hd01b, hd69a, htr014a, htr145a, htr456a, htr569a]

theorem shard_521 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr239a : m.d 3 9 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_521 m htr014a htr015a htr023a htr023b htr034a htr034b htr034c htr035a htr035b htr035c htr036b htr036c htr123b htr134b htr135b htr235a htr236a htr239a

#print axioms shard_521
end Jsp404.NoSatElevenDBMTerminal
