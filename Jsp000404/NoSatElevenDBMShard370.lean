import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_370 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr158a : m.d 5 8 + lam ≤ m.d 1 5)
    (htr159a : m.d 5 9 + lam ≤ m.d 1 5)
    (htr358c : m.d 3 8 < m.d 3 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd16a := (m.hrange 1 6 (by decide)).1
  obtain ⟨hd38a, hd38braw⟩ := m.hrange 3 8 (by decide)
  have hd38b : m.d 3 8 < 4*lam := by
    linarith only [hd38braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr016c, htr018b, htr068c])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, htr017c, htr018b, htr078c])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
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
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, hc789yx, htr017a, htr018a, htr178c, htr179a])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
    linarith only [hlam, hc7810yx, htr017a, htr018a, htr1710a, htr178c])
  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, hc123yz, htr013a, htr018a, htr138c, htr238a])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hc136yz, htr016a, htr018a, htr168c, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, hc137yz, htr017a, htr018a, htr178c, htr378a])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hc167yz, htr017a, htr018a, htr178c, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  rcases m.htr 2 3 6 (by decide) (by decide) with
    ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
  ·
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hd13a, hd68b, htr137a, htr236a, htr237a, htr368a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd12a, hd78b, htr123a, htr236a, htr367a, htr678a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc136yz, htr167b, htr179a, htr367a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd16a, hd78b, htr167a, htr378a, htr379a, htr679a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
      linarith only [hlam, hc136yz, htr167b, htr1710a, htr367a, htr6710a])
    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
      linarith only [hlam, hd16a, hd78b, htr167a, htr3710a, htr378a, htr6710a])
    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd12a, hd89b, htr123a, htr236a, htr368a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hd12a, hd68b, htr012a, htr018a, htr189a, htr689a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, htr678c, htr689a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hd12a, hd910b, htr123a, htr237a, htr379a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc124xy, hc789zy, htr123a, htr145a, htr237a, htr379a, htr458a, htr589a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr459a, htr459b, htr459c, _, _⟩
        linarith only [hlam, hc125xy, hc579yz, htr123a, htr158a, htr237a, htr379a, htr458a, htr459a])
      obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
      rcases m.htr 5 9 10 (by decide) (by decide) with
        ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      ·
        linarith only [hlam, hd56a, hd79b, htr456a, htr459a, htr5910a, htr7910a]
      ·
        linarith only [hlam, hc125xy, hc789zy, htr123a, htr159a, htr237a, htr379a, htr5910a, htr8910a]
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc125xy, hc7910zy, htr123a, htr158a, htr237a, htr3710a, htr589a, htr8910a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hd56a, hd68b, htr456a, htr458a, htr589a, htr689a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr459a, htr459b, htr459c, _, _⟩
        linarith only [hlam, hc125xy, hc568yz, htr123a, htr159a, htr236a, htr368a, htr458a, htr459a])
      obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
      rcases m.htr 5 9 10 (by decide) (by decide) with
        ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      ·
        linarith only [hlam, hc128xy, hc579yz, htr123a, htr189a, htr237a, htr379a, htr5910a, htr8910a]
      ·
        linarith only [hlam, hc124xy, hc7910zy, htr123a, htr145a, htr237a, htr3710a, htr459a, htr5910a]
  ·
    have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr237a, htr237b, htr237c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr136a, htr236a, htr237a, htr378a])
    obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc123yz, htr136b, htr167a, htr236a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hc123yz, htr137b, htr179a, htr237a, htr379a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
      linarith only [hlam, hc123yz, htr137b, htr1710a, htr237a, htr3710a])
    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
    have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr389a, htr389b, htr389c, _, _⟩
      linarith only [hlam, hd13a, hd89b, htr136a, htr236a, htr238a, htr389a])
    obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hd12a, hd38b, htr012a, htr018a, htr189a, htr389a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr137a, htr379a, htr678a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr137a, htr3710a, htr6710a, htr678a])
    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, htr378c, htr389a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hd13a, hd910b, htr136a, htr367a, htr679a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc134xy, hc789zy, htr136a, htr145a, htr367a, htr458a, htr589a, htr679a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr459a, htr459b, htr459c, _, _⟩
        linarith only [hlam, hc135xy, hc579yz, htr136a, htr158a, htr367a, htr458a, htr459a, htr679a])
      obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
      rcases m.htr 5 9 10 (by decide) (by decide) with
        ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      ·
        linarith only [hlam, hd56a, hd79b, htr456a, htr459a, htr5910a, htr7910a]
      ·
        linarith only [hlam, hc135xy, hc789zy, htr136a, htr159a, htr367a, htr5910a, htr679a, htr8910a]
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc135xy, hc7910zy, htr136a, htr158a, htr367a, htr589a, htr6710a, htr8910a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc345zy, htr358c, htr389a, htr458a, htr589a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr459a, htr459b, htr459c, _, _⟩
        linarith only [hlam, hc135xy, hc358zy, htr136a, htr159a, htr236a, htr238a, htr458a, htr459a])
      obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
      rcases m.htr 5 9 10 (by decide) (by decide) with
        ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      ·
        linarith only [hlam, hc138xy, hc579yz, htr136a, htr189a, htr367a, htr5910a, htr679a, htr8910a]
      ·
        linarith only [hlam, hc134xy, hc7910zy, htr136a, htr145a, htr367a, htr459a, htr5910a, htr6710a]

theorem shard_370 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr158a : m.d 5 8 + lam ≤ m.d 1 5)
    (htr159a : m.d 5 9 + lam ≤ m.d 1 5)
    (htr358c : m.d 3 8 < m.d 3 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_370 m htr012a htr013a htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr123a htr136a htr136b htr137a htr137b htr138c htr145a htr158a htr159a htr358c htr456a

#print axioms shard_370
end Jsp404.NoSatElevenDBMTerminal
