import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_101 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, htr023c, htr038a, htr238a])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, htr034c, htr038b, htr048c])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr035c, htr038b, htr058c])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr036c, htr038b, htr068c])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, hc012yz, htr023a, htr123c, htr138a, htr238a])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, htr034b, htr048a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc458xy, htr023c, htr034a, htr238a, htr345a, htr348c])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc348xy, htr134c, htr138a, htr145a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, htr035b, htr058a, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc568xy, htr023c, htr035a, htr238a, htr356a, htr358c])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc358xy, htr135c, htr138a, htr156a, htr356a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, htr036b, htr068a, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc345yz, htr235a, htr238a, htr358c, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd01a, hd58b, htr015a, htr156a, htr456a, htr458a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 8 (by decide) (by decide) with
    ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
  ·
    linarith only [hlam, hd01a, hd68b, htr014a, htr145a, htr456a, htr568a]
  ·
    linarith only [hlam, hc356yz, htr236a, htr238a, htr368c, htr568a]

theorem shard_101 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    : False :=
  proof_shard_101 m htr014a htr015a htr023a htr023c htr034a htr034b htr034c htr035a htr035b htr035c htr036b htr036c htr123c htr134c htr135c htr235a htr236a htr238a

#print axioms shard_101
end Jsp404.NoSatElevenDBMTerminal
