import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_103 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr2310a : m.d 2 3 + lam ≤ m.d 3 10)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc3410xy, hc3410yx, hc3410yz, hc3410zy⟩ := endpoint_caps m 3 4 10 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc3510xy, hc3510yx, hc3510yz, hc3510zy⟩ := endpoint_caps m 3 5 10 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
    linarith only [hlam, htr023c, htr0310a, htr2310a])
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
  have hforced1310 := (m.htr 1 3 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1310a, htr1310b, htr1310c, _, _⟩
    linarith only [hlam, hc012yz, htr023a, htr123c, htr1310a, htr2310a])
  obtain ⟨htr1310a, htr1310b, htr1310c, _, _⟩ := hforced1310
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, htr034b, htr0410a, htr3410a])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc4510xy, htr023c, htr034a, htr2310a, htr3410c, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc3410xy, htr1310a, htr134c, htr145a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, htr035b, htr0510a, htr3510a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc5610xy, htr023c, htr035a, htr2310a, htr3510c, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc3510xy, htr1310a, htr135c, htr156a, htr356a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, htr036b, htr0610a, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hc345yz, htr2310a, htr235a, htr3510c, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd01a, hd510b, htr015a, htr156a, htr4510a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 10 (by decide) (by decide) with
    ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
  ·
    linarith only [hlam, hd01a, hd610b, htr014a, htr145a, htr456a, htr5610a]
  ·
    linarith only [hlam, hc356yz, htr2310a, htr236a, htr3610c, htr5610a]

theorem shard_103 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr123c : m.d 1 3 < m.d 1 2)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr2310a : m.d 2 3 + lam ≤ m.d 3 10)
    : False :=
  proof_shard_103 m htr014a htr015a htr023a htr023c htr034a htr034b htr034c htr035a htr035b htr035c htr036b htr036c htr123c htr134c htr135c htr235a htr236a htr2310a

#print axioms shard_103
end Jsp404.NoSatElevenDBMTerminal
