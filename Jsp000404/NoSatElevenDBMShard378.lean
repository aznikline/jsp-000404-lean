import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_378 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd15a := (m.hrange 1 5 (by decide)).1
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr015c, htr018b, htr058c])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr016c, htr018b, htr068c])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, htr017c, htr018b, htr078c])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
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
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc678xy, htr016a, htr018a, htr167a, htr168c])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, htr017b, htr078a, htr178a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc135yz, htr015a, htr018a, htr158c, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hc136yz, htr016a, htr018a, htr168c, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc156yz, htr016a, htr018a, htr168c, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hc167yz, htr017a, htr018a, htr178c, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr135a, htr356a, htr567a, htr678a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hc123yz, htr135b, htr156a, htr235a, htr356a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd13a, hd58b, htr136a, htr235a, htr236a, htr358a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    rcases m.htr 3 6 7 (by decide) (by decide) with
      ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
    ·
      linarith only [hlam, hd12a, hd78b, htr123a, htr236a, htr367a, htr678a]
    ·
      linarith only [hlam, hd15a, hd68b, htr156a, htr367a, htr368a, htr567a]
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc135yz, htr156b, htr167a, htr356a, htr567a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced235 := (m.htr 2 3 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr235a, htr235b, htr235c, _, _⟩
      linarith only [hlam, hd12a, hd68b, htr123a, htr235a, htr356a, htr568a])
    obtain ⟨htr235a, htr235b, htr235c, _, _⟩ := hforced235
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd13a, hd68b, htr135a, htr235a, htr236a, htr368a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    rcases m.htr 3 6 7 (by decide) (by decide) with
      ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
    ·
      linarith only [hlam, hd13a, hd68b, htr136a, htr367a, htr567a, htr568a]
    ·
      linarith only [hlam, hc123yz, htr136b, htr167a, htr236a, htr367a]

theorem shard_378 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    : False :=
  proof_shard_378 m htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr123a htr135a htr135b htr136a htr136b

#print axioms shard_378
end Jsp404.NoSatElevenDBMTerminal
