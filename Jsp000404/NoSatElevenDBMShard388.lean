import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_388 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  obtain ⟨hd48a, hd48braw⟩ := m.hrange 4 8 (by decide)
  have hd48b : m.d 4 8 < 4*lam := by
    linarith only [hd48braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, htr012c, htr018b, htr028c])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, htr013c, htr018b, htr038c])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, htr014c, htr018b, htr048c])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr015c, htr018b, htr058c])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr016c, htr018b, htr068c])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, htr012b, htr028a, htr128a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced123 := (m.htr 1 2 3 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr123a, htr123b, htr123c, _, _⟩
    linarith only [hlam, hc238xy, htr012a, htr018a, htr123a, htr128c])
  obtain ⟨htr123a, htr123b, htr123c, _, _⟩ := hforced123
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, htr013b, htr038a, htr138a])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hc348xy, htr013a, htr018a, htr134a, htr138c])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hc358xy, htr013a, htr018a, htr135a, htr138c])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, htr014b, htr048a, htr148a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc458xy, htr014a, htr018a, htr145a, htr148c])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, htr015b, htr058a, htr158a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc568xy, htr015a, htr018a, htr156a, htr158c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, htr016b, htr068a, htr168a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc134yz, htr014a, htr018a, htr148c, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc135yz, htr015a, htr018a, htr158c, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc145yz, htr015a, htr018a, htr158c, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc156yz, htr016a, htr018a, htr168c, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  rcases m.htr 2 3 4 (by decide) (by decide) with
    ⟨htr234a, htr234b, htr234c, _, _⟩ | ⟨htr234a, htr234b, htr234c, _, _⟩
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13a, hd48b, htr135a, htr234a, htr235a, htr348a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr345a, htr345b, htr345c, _, _⟩
      linarith only [hlam, hd12a, hd58b, htr123a, htr234a, htr345a, htr458a])
    obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd12a, hd68b, htr123a, htr235a, htr356a, htr568a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hd14a, hd58b, htr145a, htr356a, htr358a, htr456a]
    ·
      linarith only [hlam, hc134yz, htr145b, htr156a, htr345a, htr456a]
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13a, hd58b, htr134a, htr234a, htr235a, htr358a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr345a, htr345b, htr345c, _, _⟩
      linarith only [hlam, hc123yz, htr134b, htr145a, htr234a, htr345a])
    obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc123yz, htr135b, htr156a, htr235a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hd13a, hd68b, htr134a, htr345a, htr456a, htr568a]
    ·
      linarith only [hlam, hd13a, hd58b, htr135a, htr356a, htr456a, htr458a]

theorem shard_388 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    : False :=
  proof_shard_388 m htr012a htr012b htr012c htr013a htr013b htr013c htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr018a htr018b

#print axioms shard_388
end Jsp404.NoSatElevenDBMTerminal
