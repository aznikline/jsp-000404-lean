import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_292 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd15a, hd15braw⟩ := m.hrange 1 5 (by decide)
  have hd15b : m.d 1 5 < 4*lam := by
    linarith only [hd15braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < 4*lam := by
    linarith only [hd16braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc158xy, hc158yx, hc158yz, hc158zy⟩ := endpoint_caps m 1 5 8 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc479xy, hc479yx, hc479yz, hc479zy⟩ := endpoint_caps m 4 7 9 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr015b, htr018c, htr058b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr016b, htr018c, htr068b])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, htr017b, htr018c, htr078b])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, htr015c, htr058a, htr158a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc568yx, htr015a, htr018a, htr156a, htr158b])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc578yx, htr015a, htr018a, htr157a, htr158b])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, htr016c, htr068a, htr168a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc678yx, htr016a, htr018a, htr167a, htr168b])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, htr017c, htr078a, htr178a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, hc789xy, htr017a, htr018a, htr178b, htr179a])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
    linarith only [hlam, hc7810xy, htr017a, htr018a, htr1710a, htr178b])
  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc125zy, htr015a, htr018a, htr158b, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc156zy, htr016a, htr018a, htr168b, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hc157zy, htr017a, htr018a, htr178b, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hc167zy, htr017a, htr018a, htr178b, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hc125zy, htr156c, htr167a, htr256a, htr567a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd15b, hd68a, htr157a, htr256a, htr257a, htr568a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc156zy, htr167c, htr179a, htr567a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd16b, hd78a, htr167a, htr578a, htr579a, htr679a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
      linarith only [hlam, hc156zy, htr167c, htr1710a, htr567a, htr6710a])
    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
      linarith only [hlam, hd16b, hd78a, htr167a, htr5710a, htr578a, htr6710a])
    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd16b, hd89a, htr167a, htr567a, htr568a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hd12b, hd68a, htr012a, htr018a, htr189a, htr689a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, htr678b, htr689a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hd12b, hd910a, htr125a, htr257a, htr579a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc124yx, hc7910yz, htr125a, htr148a, htr257a, htr489a, htr5710a, htr8910a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hd45b, hd68a, htr345a, htr348a, htr489a, htr689a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc146xy, hc468zy, htr149a, htr167a, htr348a, htr349a, htr567a, htr568a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      rcases m.htr 4 9 10 (by decide) (by decide) with
        ⟨htr4910a, htr4910b, htr4910c, _, _⟩ | ⟨htr4910a, htr4910b, htr4910c, _, _⟩
      ·
        linarith only [hlam, hc123yx, hc7910yz, htr125a, htr134a, htr257a, htr349a, htr4910a, htr5710a]
      ·
        linarith only [hlam, hc128yx, hc479zy, htr125a, htr189a, htr257a, htr4910a, htr579a, htr8910a]
    ·
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc478zy, htr489a, htr789b, htr7910a, htr8910a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc123yx, hc789yz, htr125a, htr134a, htr257a, htr348a, htr489a, htr579a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc124yx, hc479zy, htr125a, htr148a, htr257a, htr348a, htr349a, htr579a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      rcases m.htr 4 9 10 (by decide) (by decide) with
        ⟨htr4910a, htr4910b, htr4910c, _, _⟩ | ⟨htr4910a, htr4910b, htr4910c, _, _⟩
      ·
        linarith only [hlam, hc124yx, hc789yz, htr125a, htr149a, htr257a, htr4910a, htr579a, htr8910a]
      ·
        linarith only [hlam, hd45b, hd79a, htr345a, htr349a, htr4910a, htr7910a]
  ·
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hd12b, hd78a, htr125a, htr256a, htr567a, htr678a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hd15b, hd78a, htr156a, htr256a, htr257a, htr578a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hc125zy, htr157c, htr179a, htr257a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
      linarith only [hlam, hc125zy, htr157c, htr1710a, htr257a, htr5710a])
    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd15b, hd89a, htr156a, htr256a, htr258a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hd12b, hd58a, htr012a, htr018a, htr189a, htr589a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd15b, hd78a, htr157a, htr579a, htr678a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
      linarith only [hlam, hd15b, hd78a, htr157a, htr5710a, htr6710a, htr678a])
    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, htr578b, htr589a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hd15b, hd910a, htr156a, htr567a, htr679a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc145xy, hc7910yz, htr148a, htr156a, htr489a, htr567a, htr6710a, htr8910a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hd45b, hd58a, htr345a, htr348a, htr489a, htr589a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc145xy, hc478zy, htr149a, htr156a, htr348a, htr349a, htr567a, htr678a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      rcases m.htr 4 9 10 (by decide) (by decide) with
        ⟨htr4910a, htr4910b, htr4910c, _, _⟩ | ⟨htr4910a, htr4910b, htr4910c, _, _⟩
      ·
        linarith only [hlam, hc135xy, hc7910yz, htr134a, htr156a, htr349a, htr4910a, htr567a, htr6710a]
      ·
        linarith only [hlam, hc158yx, hc479zy, htr156a, htr189a, htr4910a, htr567a, htr679a, htr8910a]
    ·
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc478zy, htr489a, htr789b, htr7910a, htr8910a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc135xy, hc789yz, htr134a, htr156a, htr348a, htr489a, htr567a, htr679a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc145xy, hc479zy, htr148a, htr156a, htr348a, htr349a, htr567a, htr679a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      rcases m.htr 4 9 10 (by decide) (by decide) with
        ⟨htr4910a, htr4910b, htr4910c, _, _⟩ | ⟨htr4910a, htr4910b, htr4910c, _, _⟩
      ·
        linarith only [hlam, hc145xy, hc789yz, htr149a, htr156a, htr4910a, htr567a, htr679a, htr8910a]
      ·
        linarith only [hlam, hd45b, hd79a, htr345a, htr349a, htr4910a, htr7910a]

theorem shard_292 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_292 m htr012a htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018c htr125a htr134a htr148a htr149a htr345a

#print axioms shard_292
end Jsp404.NoSatElevenDBMTerminal
