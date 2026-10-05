import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_299 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr048c : m.d 0 8 < m.d 4 8)
    (htr049c : m.d 0 9 < m.d 4 9)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr057b : m.d 5 7 < m.d 0 7)
    (htr058b : m.d 5 8 < m.d 0 8)
    (htr059b : m.d 5 9 < m.d 0 9)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr148b : m.d 1 4 < m.d 1 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr156b : m.d 5 6 < m.d 1 6)
    (htr157b : m.d 5 7 < m.d 1 7)
    (htr158b : m.d 5 8 < m.d 1 8)
    (htr159b : m.d 5 9 < m.d 1 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd710a, hd710braw⟩ := m.hrange 7 10 (by decide)
  have hd710b : m.d 7 10 < 4*lam := by
    linarith only [hd710braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc148xy, hc148yx, hc148yz, hc148zy⟩ := endpoint_caps m 1 4 8 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  rcases m.htr 3 4 7 (by decide) (by decide) with
    ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
  ·
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr346c, htr347b, htr367c])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, htr346b, htr367a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc678yx, htr346a, htr347a, htr467c, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hc679yx, htr346a, htr347a, htr467c, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd14a, hd78b, htr146a, htr346a, htr347a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd14a, hd79b, htr146a, htr346a, htr347a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    rcases m.htr 5 7 8 (by decide) (by decide) with
      ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
    ·
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc457zy, htr347a, htr348a, htr478b, htr578a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd14a, hd89b, htr146a, htr346a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hd14a, hd810b, htr146a, htr346a, htr348a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc457zy, htr478c, htr489a, htr578a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc457zy, htr158b, htr189a, htr478a, htr578b, htr789a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc124yx, hc489zy, htr012a, htr018a, htr146a, htr189a, htr346a, htr349a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        linarith only [hlam, hc457zy, htr478c, htr4810a, htr578a, htr7810a])
      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hc457zy, htr158b, htr1810a, htr478a, htr578b, htr7810a])
      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc124yx, hc8910yz, htr012a, htr018a, htr146a, htr1810a, htr469a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hc124yx, hc689zy, htr012a, htr018a, htr149a, htr189a, htr4910a, htr6910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hd45b, hd89a, htr345a, htr349a, htr4910a, htr8910a]
      ·
        linarith only [hlam, hd12b, hd910a, htr012a, htr018a, htr189a, htr8910a]
    ·
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc124yx, hc478zy, htr012a, htr017a, htr146a, htr157b, htr346a, htr348a, htr578a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd12b, hd89a, htr012a, htr017a, htr157b, htr578a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd45b, hd78a, htr345a, htr348a, htr489a, htr789a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc124yx, hc678zy, htr012a, htr017a, htr148a, htr157b, htr489a, htr578a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc124yx, hc789yz, htr012a, htr017a, htr146a, htr179a, htr468a, htr689a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hc124yx, hc8910yx, htr012a, htr018a, htr146a, htr1810a, htr468a, htr689a])
      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc147yz, htr179a, htr347a, htr349a, htr479b])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hc134yz, htr148b, htr1810a, htr348a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd14a, hd910b, htr146a, htr346a, htr349a, htr4910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hc124yx, hc678zy, htr012a, htr017a, htr148a, htr157b, htr4810a, htr578a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
        linarith only [hlam, hc124yx, hc8910zy, htr012a, htr019a, htr146a, htr1910a, htr468a, htr6810a])
      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
      rcases m.htr 7 9 10 (by decide) (by decide) with
        ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      ·
        linarith only [hlam, hc147yz, htr179a, htr479c, htr4910a, htr7910a]
      ·
        linarith only [hlam, hc147yz, htr179b, htr1910a, htr479a, htr7910a]
  ·
    rcases m.htr 3 4 8 (by decide) (by decide) with
      ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
    ·
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr346c, htr348b, htr368c])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr347c, htr348b, htr378c])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr346b, htr368a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc678xy, htr346a, htr348a, htr467a, htr468c])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, htr347b, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc789yx, htr347a, htr348a, htr478c, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hc7810yx, htr347a, htr348a, htr4710a, htr478c])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd14a, hd89b, htr146a, htr346a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd14a, hd67b, htr146a, htr346a, htr348a, htr478c, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd14a, hd78b, htr147a, htr479a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc124yx, hc789zy, htr012a, htr018a, htr146a, htr189a, htr467a, htr679a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc148yz, htr189a, htr348a, htr349a, htr489b])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd14a, hd910b, htr146a, htr346a, htr349a, htr4910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        linarith only [hlam, hd14a, hd78b, htr147a, htr4710a, htr6710a, htr678a])
      obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
        linarith only [hlam, hc124yx, hc7910zy, htr012a, htr019a, htr146a, htr1910a, htr467a, htr6710a])
      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc148yz, htr189a, htr489c, htr4910a, htr8910a]
      ·
        linarith only [hlam, hc148yz, htr189b, htr1910a, htr489a, htr8910a]
    ·
      rcases m.htr 3 4 9 (by decide) (by decide) with
        ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
      ·
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr346c, htr349b, htr369c])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr347c, htr349b, htr379c])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, htr348c, htr349b, htr389c])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, htr346b, htr369a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc679xy, htr346a, htr349a, htr467a, htr469c])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, htr347b, htr379a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc789xy, htr347a, htr349a, htr478a, htr479c])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, htr348b, htr389a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd14a, hd67b, htr146a, htr346a, htr349a, htr479c, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd14a, hd79b, htr147a, htr478a, htr678a, htr679a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd14a, hd89b, htr146a, htr467a, htr678a, htr789a]
        ·
          linarith only [hlam, hd14a, hd78b, htr146a, htr346a, htr349a, htr489c, htr789a]
      ·
        rcases m.htr 3 4 10 (by decide) (by decide) with
          ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
        ·
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr3410b, htr346c, htr3610c])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr3410b, htr347c, htr3710c])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, htr3410b, htr348c, htr3810c])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, htr346b, htr3610a, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc6710xy, htr3410a, htr346a, htr4610c, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, htr347b, htr3710a, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc7810xy, htr3410a, htr347a, htr4710c, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, htr348b, htr3810a, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hd14a, hd67b, htr146a, htr3410a, htr346a, htr4710c, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd14a, hd710b, htr147a, htr478a, htr6710a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd14a, hd810b, htr146a, htr467a, htr678a, htr7810a]
          ·
            linarith only [hlam, hd14a, hd78b, htr146a, htr3410a, htr346a, htr4810c, htr7810a]
        ·
          rcases m.htr 4 6 7 (by decide) (by decide) with
            ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, htr046c, htr067a, htr467a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, htr146c, htr167a, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc134yz, htr146a, htr346c, htr367a, htr467a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            rcases m.htr 4 6 8 (by decide) (by decide) with
              ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
            ·
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr047c, htr078a, htr478a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, htr147c, htr178a, htr478a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc134yz, htr147a, htr347c, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc124yx, hc789yx, htr012a, htr017a, htr146a, htr179a, htr467a, htr678a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                    linarith only [hlam, hc124yx, hc7810yx, htr012a, htr017a, htr146a, htr1710a, htr467a, htr678a])
                  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc134yz, htr147b, htr179a, htr347a, htr479a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc134yz, htr147b, htr1710a, htr347a, htr4710a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd14a, hd78b, htr147a, htr479a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc124yx, hc789zy, htr012a, htr018a, htr146a, htr189a, htr467a, htr679a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc134yz, htr148b, htr189a, htr348a, htr489a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd14a, hd78b, htr147a, htr4710a, htr6710a, htr678a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                    linarith only [hlam, hc124yx, hc7910zy, htr012a, htr019a, htr146a, htr1910a, htr467a, htr6710a])
                  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd14a, hd89b, htr146a, htr467a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd14a, hd910b, htr146a, htr467a, htr679a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd14a, hd79b, htr148a, htr489a, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hc178yz, htr189b, htr1910a, htr789a, htr8910a]
                ·
                  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                    linarith only [hlam, hc679yx, htr367b, htr369a, htr378a, htr678a])
                  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd14a, hd79b, htr147a, htr478a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  rcases m.htr 5 7 9 (by decide) (by decide) with
                    ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, hc567yz, htr047c, htr079a, htr478a, htr579a, htr678a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, hc567yz, htr378a, htr379a, htr579a, htr678a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                    rcases m.htr 5 7 10 (by decide) (by decide) with
                      ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    ·
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                          linarith only [hlam, hc124yx, hc8910yx, htr012a, htr018a, htr147a, htr1810a, htr478a, htr789a])
                        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                          linarith only [hlam, hc167yz, htr178b, htr1810a, htr378c, htr3810a, htr678a])
                        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hd14a, hd68b, htr147a, htr478a, htr689a, htr789a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                          linarith only [hlam, hd13a, hd89b, htr138a, htr3810a, htr6810a, htr689a])
                        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                          linarith only [hlam, hc124yx, hc8910zy, htr012a, htr019a, htr146a, htr1910a, htr468a, htr6810a])
                        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hc567yz, htr159b, htr1910a, htr579b, htr679a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd14a, hd910b, htr147a, htr478a, htr789a, htr8910a]
                        ·
                          linarith only [hlam, hd13a, hd89b, htr137a, htr379a, htr7910a, htr8910a]
                      ·
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, hc067yz, htr078b, htr089a, htr678a, htr789a])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc167yz, htr178b, htr189a, htr678a, htr789a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc124yx, hc8910xy, htr012a, htr018a, htr147a, htr189a, htr478a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, hc067yz, htr078b, htr0810a, htr678a, htr7810a])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                          linarith only [hlam, hd45b, hd89a, htr048c, htr0810a, htr1810a, htr189a, htr345a, htr348a])
                        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hc123yx, hc8910yz, htr012a, htr018a, htr136a, htr1810a, htr369a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                          linarith only [hlam, hc123yx, hc689zy, htr012a, htr018a, htr139a, htr189a, htr3910a, htr6910a])
                        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                          linarith only [hlam, hc567yz, htr059b, htr0910a, htr379c, htr3910a, htr579b, htr679a])
                        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd45b, hd89a, htr049c, htr0910a, htr345a, htr349a, htr8910a]
                        ·
                          linarith only [hlam, hd45b, hd910a, htr048c, htr089a, htr345a, htr348a, htr8910a]
                    ·
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, htr057b, htr0710a, htr5710a])
                      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, htr0710c, htr078b, htr0810b])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                        linarith only [hlam, htr0710c, htr079b, htr0910b])
                      obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                        linarith only [hlam, hd45b, hd710a, htr048c, htr0810a, htr157b, htr178b, htr1810a, htr345a, htr348a, htr5710a])
                      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hc124yx, hc8910yx, htr012a, htr018a, htr147a, htr1810a, htr478a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, hc067yz, htr078b, htr089a, htr678a, htr789a])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd45b, hd89a, htr049c, htr0910a, htr345a, htr349a, htr8910a]
                      ·
                        linarith only [hlam, hd45b, hd910a, htr048c, htr089a, htr345a, htr348a, htr8910a]
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, htr057b, htr079a, htr579a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr078b, htr079c, htr089b])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hd45b, hd79a, htr048c, htr089a, htr157b, htr178b, htr189a, htr345a, htr348a, htr579a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, htr137c, htr157b, htr379a, htr579a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                    have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      linarith only [hlam, hc124yx, hc8910xy, htr012a, htr018a, htr147a, htr189a, htr478a, htr7810a])
                    obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc067yz, htr078b, htr0810a, htr678a, htr7810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hd45b, hd79a, htr048c, htr0810a, htr157b, htr178b, htr1810a, htr345a, htr348a, htr579a])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc123yx, hc8910yz, htr012a, htr018a, htr136a, htr1810a, htr369a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                      linarith only [hlam, hc123yx, hc679zy, htr012a, htr017a, htr139a, htr157b, htr3910a, htr579a, htr6910a])
                    obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd67b, hd89a, htr378a, htr379c, htr3910a, htr678a, htr8910a]
                    ·
                      linarith only [hlam, hd45b, hd910a, htr048c, htr089a, htr345a, htr348a, htr8910a]
              ·
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc134yz, htr147b, htr178a, htr347a, htr478a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, htr347b, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd45b, hd89a, htr345a, htr347a, htr478a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hd45b, hd78a, htr345a, htr348a, htr489a, htr789a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc124yx, hc678zy, htr012a, htr017a, htr148a, htr178a, htr489a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc124yx, hc789yz, htr012a, htr017a, htr146a, htr179a, htr468a, htr689a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc124yx, hc8910yx, htr012a, htr018a, htr146a, htr1810a, htr468a, htr689a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hd45b, hd78a, htr178a, htr179a, htr345a, htr347c, htr379a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                  linarith only [hlam, hc128yx, hc789xy, htr012a, htr017a, htr178a, htr1810a, htr378c, htr379a, htr3810a])
                obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc123yx, hc678zy, htr012a, htr017a, htr138a, htr178a, htr3810a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                  linarith only [hlam, hc124yx, hc8910zy, htr012a, htr019a, htr146a, htr1910a, htr468a, htr6810a])
                obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc789xy, htr178a, htr179b, htr1910a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd14a, hd910b, htr146a, htr468a, htr689a, htr8910a]
                ·
                  linarith only [hlam, hd78a, hd89b, htr178a, htr179a, htr7910a, htr8910a]
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc034yz, htr046b, htr068a, htr346a, htr468a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, htr067b, htr068c, htr078b])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc134yz, htr146b, htr168a, htr346a, htr468a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hd45b, hd68a, htr047c, htr078a, htr167b, htr168a, htr178a, htr345a, htr347a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, htr346b, htr368a, htr468a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc124yx, hc789xy, htr012a, htr017a, htr146a, htr178a, htr467a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hc678yx, htr067b, htr068a, htr079a, htr679a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hd45b, hd68a, htr047c, htr079a, htr167b, htr168a, htr179a, htr345a, htr347a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                linarith only [hlam, hc124yx, hc7810xy, htr012a, htr017a, htr146a, htr178a, htr467a, htr6710a])
              obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, hc678yx, htr067b, htr068a, htr0710a, htr6710a])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hd45b, hd68a, htr047c, htr0710a, htr167b, htr168a, htr1710a, htr345a, htr347a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd45b, hd89a, htr345a, htr346a, htr468a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc678yx, htr367a, htr368c, htr389a, htr689a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd45b, hd910a, htr047c, htr079a, htr345a, htr347a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hd45b, hd79a, htr345a, htr349a, htr4910a, htr7910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc123yx, hc7910yz, htr012a, htr017a, htr138a, htr1710a, htr389a, htr8910a]
              ·
                linarith only [hlam, hc124yx, hc789yz, htr012a, htr017a, htr149a, htr179a, htr4910a, htr8910a]
          ·
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc134yz, htr146b, htr167a, htr346a, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd45b, hd56a, htr345a, htr346a, htr467a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd45b, hd78a, htr345a, htr346a, htr467a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hd45b, hd79a, htr345a, htr346a, htr467a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr479a, htr679a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr046c, htr068a, htr345a, htr346a, htr567a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr345a, htr346c, htr368a, htr567a, htr568a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              rcases m.htr 5 6 9 (by decide) (by decide) with
                ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hd45b, hd67a, htr046c, htr069a, htr345a, htr346a, htr567a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                  linarith only [hlam, hc678xy, htr368a, htr369a, htr567a, htr569a])
                obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                rcases m.htr 5 6 10 (by decide) (by decide) with
                  ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                ·
                  rcases m.htr 5 8 9 (by decide) (by decide) with
                    ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
                  ·
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hc678xy, htr567a, htr568b, htr589a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hc123yx, hc8910yx, htr012a, htr018a, htr136a, htr1810a, htr368a, htr689a])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc678xy, htr158b, htr1810a, htr567a, htr568b, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                      linarith only [hlam, hc123yx, hc8910zy, htr012a, htr019a, htr136a, htr1910a, htr368a, htr6810a])
                    obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc679xy, htr159b, htr1910a, htr567a, htr569b, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd67a, hd910b, htr567a, htr568a, htr689a, htr8910a]
                    ·
                      linarith only [hlam, hd67a, hd89b, htr567a, htr569a, htr6910a, htr8910a]
                  ·
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc123yx, hc8910xy, htr012a, htr018a, htr136a, htr158b, htr368a, htr589a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc678xy, htr058b, htr0810a, htr567a, htr568b, htr6810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hd45b, hd67a, htr048c, htr0810a, htr158b, htr1810a, htr345a, htr348a, htr567a, htr568b])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc123yx, hc8910yz, htr012a, htr018a, htr136a, htr1810a, htr369a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                      linarith only [hlam, hc679xy, htr059b, htr0910a, htr567a, htr569b, htr6910a])
                    obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd45b, hd89a, htr049c, htr0910a, htr345a, htr349a, htr8910a]
                    ·
                      linarith only [hlam, hd12b, hd910a, htr012a, htr018a, htr158b, htr589a, htr8910a]
                ·
                  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                    linarith only [hlam, htr056b, htr0610a, htr5610a])
                  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                    linarith only [hlam, htr0610c, htr068b, htr0810b])
                  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                    linarith only [hlam, htr0610c, htr069b, htr0910b])
                  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                  have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                    linarith only [hlam, hd45b, hd67a, htr048c, htr0810a, htr158b, htr1810a, htr345a, htr348a, htr567a, htr568b])
                  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc123yx, hc8910yx, htr012a, htr018a, htr136a, htr1810a, htr368a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, hc678xy, htr058b, htr089a, htr567a, htr568b, htr689a])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd45b, hd89a, htr049c, htr0910a, htr345a, htr349a, htr8910a]
                  ·
                    linarith only [hlam, hd45b, hd910a, htr048c, htr089a, htr345a, htr348a, htr8910a]
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, htr056b, htr069a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, htr068b, htr069c, htr089b])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hd45b, hd67a, htr048c, htr089a, htr158b, htr189a, htr345a, htr348a, htr567a, htr568b])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                  linarith only [hlam, htr036c, htr056b, htr369a, htr569a])
                obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc123yx, hc8910xy, htr012a, htr018a, htr136a, htr189a, htr368a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, hc678xy, htr058b, htr0810a, htr567a, htr568b, htr6810a])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hd45b, hd67a, htr048c, htr0810a, htr158b, htr1810a, htr345a, htr348a, htr567a, htr568b])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd12b, hd910a, htr012a, htr016a, htr156b, htr569a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                  linarith only [hlam, hc689yx, htr368a, htr369c, htr3910a, htr6910a])
                obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc124yx, hc8910yz, htr012a, htr018a, htr147a, htr1810a, htr479a, htr7910a]
                ·
                  linarith only [hlam, hc123yx, hc679yz, htr012a, htr016a, htr139a, htr156b, htr3910a, htr569a, htr7910a]
            ·
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd12b, hd89a, htr012a, htr016a, htr156b, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hd45b, hd68a, htr345a, htr348a, htr489a, htr689a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd12b, hd810a, htr012a, htr016a, htr156b, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hd45b, hd68a, htr345a, htr348a, htr4810a, htr6810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc124yx, hc678yz, htr012a, htr016a, htr148a, htr156b, htr489a, htr568a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc124yx, hc689yz, htr012a, htr016a, htr147a, htr169a, htr478a, htr789a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc124yx, hc678yz, htr012a, htr016a, htr148a, htr156b, htr4810a, htr568a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc124yx, hc8910zy, htr012a, htr019a, htr147a, htr1910a, htr478a, htr7810a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc679xy, htr167a, htr169b, htr1910a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd14a, hd910b, htr147a, htr478a, htr789a, htr8910a]
              ·
                linarith only [hlam, hd67a, hd89b, htr167a, htr169a, htr6910a, htr8910a]

theorem shard_299 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr048c : m.d 0 8 < m.d 4 8)
    (htr049c : m.d 0 9 < m.d 4 9)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr057b : m.d 5 7 < m.d 0 7)
    (htr058b : m.d 5 8 < m.d 0 8)
    (htr059b : m.d 5 9 < m.d 0 9)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 4 6)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr148b : m.d 1 4 < m.d 1 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr156b : m.d 5 6 < m.d 1 6)
    (htr157b : m.d 5 7 < m.d 1 7)
    (htr158b : m.d 5 8 < m.d 1 8)
    (htr159b : m.d 5 9 < m.d 1 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    : False :=
  proof_shard_299 m htr012a htr016a htr017a htr018a htr019a htr036c htr046b htr046c htr047c htr048c htr049c htr056b htr057b htr058b htr059b htr136a htr137a htr137c htr138a htr139a htr146a htr146b htr146c htr147a htr147b htr147c htr148a htr148b htr149a htr156b htr157b htr158b htr159b htr345a htr346a htr346b htr346c

#print axioms shard_299
end Jsp404.NoSatElevenDBMTerminal
