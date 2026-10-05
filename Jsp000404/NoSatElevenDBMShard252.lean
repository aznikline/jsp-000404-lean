import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_252 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019c : m.d 0 9 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137c : m.d 1 7 < m.d 1 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < 4*lam := by
    linarith only [hd16braw, hp]
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr016b, htr019c, htr069b])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
    linarith only [hlam, htr017b, htr019c, htr079b])
  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
    linarith only [hlam, htr018b, htr019c, htr089b])
  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, htr016c, htr069a, htr169a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc679yx, htr016a, htr019a, htr167a, htr169b])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, htr017c, htr079a, htr179a])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hc789yx, htr017a, htr019a, htr178a, htr179b])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
    linarith only [hlam, htr018c, htr089a, htr189a])
  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hc136zy, htr016a, htr019a, htr169b, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
    linarith only [hlam, hc137zy, htr017a, htr019a, htr179b, htr379a])
  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hc167zy, htr017a, htr019a, htr179b, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
    linarith only [hlam, hc178zy, htr018a, htr019a, htr189b, htr789a])
  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc136zy, htr167c, htr178a, htr367a, htr678a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hd12b, hd79a, htr123a, htr236a, htr367a, htr679a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hd13b, hd79a, htr136a, htr236a, htr237a, htr379a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    rcases m.htr 3 7 8 (by decide) (by decide) with
      ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
    ·
      linarith only [hlam, hc123zy, htr137c, htr178a, htr237a, htr378a]
    ·
      linarith only [hlam, hd13b, hd79a, htr137a, htr378a, htr678a, htr679a]
  ·
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd13b, hd89a, htr136a, htr367a, htr678a, htr789a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr236a, htr236b, htr236c, _, _⟩
      linarith only [hlam, hc123zy, htr136c, htr167a, htr236a, htr367a])
    obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hd13b, hd69a, htr137a, htr236a, htr237a, htr369a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    rcases m.htr 3 7 8 (by decide) (by decide) with
      ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
    ·
      linarith only [hlam, hd16b, hd79a, htr167a, htr378a, htr379a, htr678a]
    ·
      linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]

theorem shard_252 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr019c : m.d 0 9 < m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137c : m.d 1 7 < m.d 1 3)
    : False :=
  proof_shard_252 m htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr018c htr019a htr019c htr123a htr136a htr136c htr137a htr137c

#print axioms shard_252
end Jsp404.NoSatElevenDBMTerminal
