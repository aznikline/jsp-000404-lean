import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_615 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
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
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, hc023zy, htr038a, htr134a, htr138a, htr234a])
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
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, htr014b, htr048a, htr134b, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc458xy, htr013b, htr038a, htr134a, htr345a, htr348c])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, htr015b, htr058a, htr135b, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc568xy, htr013b, htr038a, htr135a, htr356a, htr358c])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, htr016b, htr068a, htr136b, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd23a, hd45b, htr134a, htr138a, htr234a, htr358c, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd23a, hd58b, htr235a, htr356a, htr456a, htr458a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 8 (by decide) (by decide) with
    ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
  ·
    linarith only [hlam, hd23a, hd68b, htr234a, htr345a, htr456a, htr568a]
  ·
    linarith only [hlam, hd23a, hd56b, htr134a, htr138a, htr234a, htr368c, htr568a]

theorem shard_615 {lam p : ℝ} (m : ElevenModel lam p)
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
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    : False :=
  proof_shard_615 m htr013b htr014b htr015b htr016b htr034c htr035c htr036c htr134a htr134b htr135a htr135b htr136b htr138a htr234a htr235a

#print axioms shard_615
end Jsp404.NoSatElevenDBMTerminal
