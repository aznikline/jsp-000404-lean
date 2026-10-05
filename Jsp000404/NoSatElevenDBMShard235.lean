import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_235 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < 4*lam := by
    linarith only [hd14braw, hp]
  have hd48a := (m.hrange 4 8 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
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
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, htr012b, htr018c, htr028b])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, htr013b, htr018c, htr038b])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, htr014b, htr018c, htr048b])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr015b, htr018c, htr058b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr016b, htr018c, htr068b])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, htr012c, htr028a, htr128a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced123 := (m.htr 1 2 3 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr123a, htr123b, htr123c, _, _⟩
    linarith only [hlam, hc238yx, htr012a, htr018a, htr123a, htr128b])
  obtain ⟨htr123a, htr123b, htr123c, _, _⟩ := hforced123
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, htr013c, htr038a, htr138a])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hc348yx, htr013a, htr018a, htr134a, htr138b])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hc358yx, htr013a, htr018a, htr135a, htr138b])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, htr014c, htr048a, htr148a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc458yx, htr014a, htr018a, htr145a, htr148b])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, htr015c, htr058a, htr158a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc568yx, htr015a, htr018a, htr156a, htr158b])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, htr016c, htr068a, htr168a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc134zy, htr014a, htr018a, htr148b, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc135zy, htr015a, htr018a, htr158b, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc145zy, htr015a, htr018a, htr158b, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc156zy, htr016a, htr018a, htr168b, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  rcases m.htr 2 3 4 (by decide) (by decide) with
    ⟨htr234a, htr234b, htr234c, _, _⟩ | ⟨htr234a, htr234b, htr234c, _, _⟩
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13b, hd58a, htr134a, htr234a, htr235a, htr358a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr345a, htr345b, htr345c, _, _⟩
      linarith only [hlam, hc123zy, htr134c, htr145a, htr234a, htr345a])
    obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc123zy, htr135c, htr156a, htr235a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hd13b, hd58a, htr135a, htr356a, htr456a, htr458a]
    ·
      linarith only [hlam, hd13b, hd68a, htr134a, htr345a, htr456a, htr568a]
  ·
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd13b, hd48a, htr135a, htr234a, htr235a, htr348a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr345a, htr345b, htr345c, _, _⟩
      linarith only [hlam, hd12b, hd58a, htr123a, htr234a, htr345a, htr458a])
    obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd12b, hd68a, htr123a, htr235a, htr356a, htr568a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      linarith only [hlam, hc134zy, htr145c, htr156a, htr345a, htr456a]
    ·
      linarith only [hlam, hd14b, hd58a, htr145a, htr356a, htr358a, htr456a]

theorem shard_235 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr012b : m.d 0 1 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013b : m.d 0 1 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    : False :=
  proof_shard_235 m htr012a htr012b htr012c htr013a htr013b htr013c htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr018a htr018c

#print axioms shard_235
end Jsp404.NoSatElevenDBMTerminal
