import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_295 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr158a : m.d 5 8 + lam ≤ m.d 1 5)
    (htr159a : m.d 5 9 + lam ≤ m.d 1 5)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd16a := (m.hrange 1 6 (by decide)).1
  obtain ⟨hd48a, hd48braw⟩ := m.hrange 4 8 (by decide)
  have hd48b : m.d 4 8 < 4*lam := by
    linarith only [hd48braw, hp]
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
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc148xy, hc148yx, hc148yz, hc148zy⟩ := endpoint_caps m 1 4 8 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
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
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc134yz, htr014a, htr018a, htr148c, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hc146yz, htr016a, htr018a, htr168c, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hc147yz, htr017a, htr018a, htr178c, htr478a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hc167yz, htr017a, htr018a, htr178c, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd14a, hd68b, htr147a, htr346a, htr347a, htr468a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr134a, htr346a, htr467a, htr678a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc146yz, htr167b, htr179a, htr467a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd16a, hd78b, htr167a, htr478a, htr479a, htr679a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
      linarith only [hlam, hc146yz, htr167b, htr1710a, htr467a, htr6710a])
    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
      linarith only [hlam, hd16a, hd78b, htr167a, htr4710a, htr478a, htr6710a])
    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd13a, hd89b, htr134a, htr346a, htr468a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hd13a, hd68b, htr013a, htr018a, htr189a, htr689a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, htr678c, htr689a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hd13a, hd910b, htr134a, htr347a, htr479a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc123yx, hc789zy, htr125a, htr134a, htr258a, htr347a, htr479a, htr589a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr259a, htr259b, htr259c, _, _⟩
        linarith only [hlam, hc135xy, hc579yz, htr134a, htr158a, htr258a, htr259a, htr347a, htr479a])
      obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
      rcases m.htr 5 9 10 (by decide) (by decide) with
        ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      ·
        linarith only [hlam, hd56a, hd79b, htr256a, htr259a, htr5910a, htr7910a]
      ·
        linarith only [hlam, hc135xy, hc789zy, htr134a, htr159a, htr347a, htr479a, htr5910a, htr8910a]
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc135xy, hc7910zy, htr134a, htr158a, htr347a, htr4710a, htr589a, htr8910a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hd56a, hd68b, htr256a, htr258a, htr589a, htr689a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr259a, htr259b, htr259c, _, _⟩
        linarith only [hlam, hc135xy, hc568yz, htr134a, htr159a, htr258a, htr259a, htr346a, htr468a])
      obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
      rcases m.htr 5 9 10 (by decide) (by decide) with
        ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      ·
        linarith only [hlam, hc138xy, hc579yz, htr134a, htr189a, htr347a, htr479a, htr5910a, htr8910a]
      ·
        linarith only [hlam, hc123yx, hc7910zy, htr125a, htr134a, htr259a, htr347a, htr4710a, htr5910a]
  ·
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hd14a, hd78b, htr146a, htr346a, htr347a, htr478a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc134yz, htr146b, htr167a, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hc134yz, htr147b, htr179a, htr347a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
      linarith only [hlam, hc134yz, htr147b, htr1710a, htr347a, htr4710a])
    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hd14a, hd89b, htr146a, htr346a, htr348a, htr489a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hd13a, hd48b, htr013a, htr018a, htr189a, htr489a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd14a, hd78b, htr147a, htr479a, htr678a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
      linarith only [hlam, hd14a, hd78b, htr147a, htr4710a, htr6710a, htr678a])
    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, htr478c, htr489a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hd14a, hd910b, htr146a, htr467a, htr679a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc124yx, hc789zy, htr125a, htr146a, htr258a, htr467a, htr589a, htr679a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr259a, htr259b, htr259c, _, _⟩
        linarith only [hlam, hc145xy, hc579yz, htr146a, htr158a, htr258a, htr259a, htr467a, htr679a])
      obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
      rcases m.htr 5 9 10 (by decide) (by decide) with
        ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      ·
        linarith only [hlam, hd56a, hd79b, htr256a, htr259a, htr5910a, htr7910a]
      ·
        linarith only [hlam, hc145xy, hc789zy, htr146a, htr159a, htr467a, htr5910a, htr679a, htr8910a]
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc145xy, hc7910zy, htr146a, htr158a, htr467a, htr589a, htr6710a, htr8910a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hd48b, hd56a, htr256a, htr258a, htr489a, htr589a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr259a, htr259b, htr259c, _, _⟩
        linarith only [hlam, hc145xy, hc458zy, htr146a, htr159a, htr258a, htr259a, htr346a, htr348a])
      obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
      rcases m.htr 5 9 10 (by decide) (by decide) with
        ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      ·
        linarith only [hlam, hc148xy, hc579yz, htr146a, htr189a, htr467a, htr5910a, htr679a, htr8910a]
      ·
        linarith only [hlam, hc124yx, hc7910zy, htr125a, htr146a, htr259a, htr467a, htr5910a, htr6710a]

theorem shard_295 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr158a : m.d 5 8 + lam ≤ m.d 1 5)
    (htr159a : m.d 5 9 + lam ≤ m.d 1 5)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    : False :=
  proof_shard_295 m htr013a htr014a htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr125a htr134a htr146a htr146b htr147a htr147b htr148c htr158a htr159a htr256a

#print axioms shard_295
end Jsp404.NoSatElevenDBMTerminal
