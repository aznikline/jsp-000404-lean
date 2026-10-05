import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_301 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr048c : m.d 0 8 < m.d 4 8)
    (htr049c : m.d 0 9 < m.d 4 9)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr148b : m.d 1 4 < m.d 1 8)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr149c : m.d 1 9 < m.d 4 9)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr158a : m.d 1 5 + lam ≤ m.d 5 8)
    (htr159a : m.d 1 5 + lam ≤ m.d 5 9)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd14a := (m.hrange 1 4 (by decide)).1
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
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
  obtain ⟨hc057xy, hc057yx, hc057yz, hc057zy⟩ := endpoint_caps m 0 5 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc134yz, htr145b, htr157a, htr345a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc134yz, htr145b, htr158a, htr345a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc134yz, htr145b, htr159a, htr345a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd14a, hd67b, htr145a, htr345a, htr346a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hd13a, hd46b, htr013a, htr016a, htr167a, htr467a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc136xy, htr013a, htr016b, htr067a, htr167a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hd14a, hd68b, htr145a, htr345a, htr346a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hd13a, hd46b, htr013a, htr016a, htr168a, htr468a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hd14a, hd69b, htr145a, htr345a, htr346a, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, hd13a, hd46b, htr013a, htr016a, htr169a, htr469a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, hc136xy, htr013a, htr016b, htr069a, htr169a])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  rcases m.htr 3 4 7 (by decide) (by decide) with
    ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
  ·
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd14a, hd78b, htr145a, htr345a, htr347a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd14a, hd79b, htr145a, htr345a, htr347a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    rcases m.htr 3 4 8 (by decide) (by decide) with
      ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
    ·
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd14a, hd89b, htr145a, htr345a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hd14a, hd810b, htr145a, htr345a, htr348a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc246yz, htr267a, htr467c, htr478a, htr678a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc146xy, hc467zy, htr145a, htr168a, htr267a, htr268a, htr345a, htr347a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr349a, htr349b, htr349c, _, _⟩
          linarith only [hlam, hc124yx, hc489zy, htr126a, htr145a, htr268a, htr345a, htr349a, htr689a])
        obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc467zy, htr478c, htr4810a, htr678a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc467zy, htr478a, htr678b, htr6810a, htr7810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc124yx, hc8910yz, htr126a, htr145a, htr268a, htr459a, htr5910a, htr6810a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc124yx, hc589zy, htr126a, htr149a, htr268a, htr4910a, htr5910a, htr689a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd46b, hd89a, htr346a, htr349a, htr4910a, htr8910a]
        ·
          linarith only [hlam, hd12b, hd910a, htr126a, htr268a, htr689a, htr8910a]
      ·
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc124yx, hc478zy, htr126a, htr145a, htr267a, htr345a, htr348a, htr678a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc146xy, hc468zy, htr145a, htr167a, htr267a, htr268a, htr345a, htr348a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc246yz, htr268a, htr468c, htr489a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc246yz, htr268a, htr468c, htr4810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc146xy, hc478zy, htr145a, htr168a, htr345a, htr348a, htr689a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr349a, htr349b, htr349c, _, _⟩
          linarith only [hlam, hc146xy, hc489zy, htr145a, htr167a, htr345a, htr349a, htr678a, htr789a])
        obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, hc246yz, htr269a, htr346a, htr349a, htr469b])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd46b, hd910a, htr267a, htr269a, htr467a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd46b, hd69a, htr346a, htr349a, htr4910a, htr6910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc146xy, hc589zy, htr149a, htr167a, htr4910a, htr5910a, htr678a, htr789a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc146xy, hc478zy, htr145a, htr168a, htr345a, htr348a, htr6810a, htr7810a]
        ·
          linarith only [hlam, hc146xy, hc8910yz, htr145a, htr167a, htr459a, htr5910a, htr678a, htr7810a]
    ·
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc134yz, htr014a, htr018a, htr148c, htr348a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc246yz, htr268a, htr346a, htr348a, htr468b])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc467zy, htr347a, htr348a, htr478b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 2 6 7 (by decide) (by decide) with
        ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
      ·
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc246yz, htr267a, htr467c, htr479a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd46b, hd89a, htr267a, htr268a, htr467a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd46b, hd68a, htr346a, htr348a, htr489a, htr689a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc146xy, hc568zy, htr148a, htr167a, htr267a, htr268a, htr489a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc124yx, hc8910yx, htr012a, htr018a, htr145a, htr1810a, htr458a, htr589a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, hc146xy, hc689yz, htr145a, htr167a, htr267a, htr269a, htr458a, htr589a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr349a, htr349b, htr349c, _, _⟩
          linarith only [hlam, hc246yz, htr269a, htr346a, htr349a, htr469b])
        obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hc134yz, htr148b, htr1810a, htr348a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd14a, hd910b, htr145a, htr345a, htr349a, htr4910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc146xy, hc568zy, htr148a, htr167a, htr267a, htr268a, htr4810a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc246yz, htr269a, htr469c, htr4910a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc146xy, hc789yz, htr145a, htr169a, htr458a, htr589a, htr6910a, htr7910a]
        ·
          linarith only [hlam, hc146xy, hc8910zy, htr145a, htr167a, htr458a, htr5810a, htr679a, htr7910a]
      ·
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, hc146xy, hc467zy, htr145a, htr169a, htr267a, htr269a, htr345a, htr347a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr126a, htr267a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd46b, hd78a, htr346a, htr348a, htr489a, htr789a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc124yx, hc578zy, htr126a, htr148a, htr267a, htr489a, htr589a, htr678a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc124yx, hc8910yx, htr012a, htr018a, htr145a, htr1810a, htr458a, htr589a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hc134yz, htr148b, htr1810a, htr348a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc124yx, hc578zy, htr126a, htr148a, htr267a, htr4810a, htr5810a, htr678a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc124yx, hc789yz, htr126a, htr145a, htr267a, htr458a, htr589a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr349a, htr349b, htr349c, _, _⟩
          linarith only [hlam, hc467zy, htr347a, htr349a, htr479b, htr679a])
        obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd14a, hd910b, htr145a, htr345a, htr349a, htr4910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc124yx, hc8910zy, htr126a, htr145a, htr269a, htr458a, htr5810a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc467zy, htr479c, htr4910a, htr679a, htr7910a]
        ·
          linarith only [hlam, hc467zy, htr479a, htr679b, htr6910a, htr7910a]
  ·
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc134yz, htr014a, htr017a, htr147c, htr347a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc246yz, htr267a, htr346a, htr347a, htr467b])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    rcases m.htr 3 4 8 (by decide) (by decide) with
      ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
    ·
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr347c, htr348b, htr378c])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
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
        linarith only [hlam, hd14a, hd89b, htr145a, htr345a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd14a, hd57b, htr145a, htr345a, htr348a, htr478c, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd14a, hd78b, htr147a, htr479a, htr578a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hd14a, hd78b, htr147a, htr4710a, htr5710a, htr578a])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, htr478c, htr489a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd14a, hd910b, htr145a, htr457a, htr579a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc246yz, htr268a, htr468c, htr489a, htr689a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, hc146xy, hc468zy, htr145a, htr169a, htr268a, htr269a, htr345a, htr348a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc124yx, hc7910zy, htr126a, htr145a, htr269a, htr457a, htr5710a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc468zy, htr489a, htr689b, htr6910a, htr8910a]
      ·
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc124yx, hc789zy, htr126a, htr145a, htr268a, htr457a, htr579a, htr689a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, hc146xy, hc679yz, htr145a, htr168a, htr268a, htr269a, htr457a, htr579a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd67a, hd79b, htr267a, htr269a, htr6910a, htr7910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc146xy, hc789zy, htr145a, htr169a, htr457a, htr579a, htr6910a, htr8910a]
        ·
          linarith only [hlam, hc146xy, hc7910zy, htr145a, htr168a, htr457a, htr5710a, htr689a, htr8910a]
    ·
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc134yz, htr014a, htr018a, htr148c, htr348a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      rcases m.htr 3 4 9 (by decide) (by decide) with
        ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
      ·
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr347c, htr349b, htr379c])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, htr348c, htr349b, htr389c])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
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
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd14a, hd57b, htr145a, htr345a, htr349a, htr479c, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd14a, hd79b, htr147a, htr478a, htr578a, htr579a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd14a, hd89b, htr145a, htr457a, htr578a, htr789a]
        ·
          linarith only [hlam, hd14a, hd78b, htr145a, htr345a, htr349a, htr489c, htr789a]
      ·
        have hforced019 := (m.htr 0 1 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr019a, htr019b, htr019c, _, _⟩
          linarith only [hlam, hc134yz, htr014a, htr019a, htr149c, htr349a])
        obtain ⟨htr019a, htr019b, htr019c, _, _⟩ := hforced019
        rcases m.htr 3 4 10 (by decide) (by decide) with
          ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
        ·
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr3410b, htr347c, htr3710c])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, htr3410b, htr348c, htr3810c])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
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
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hd14a, hd57b, htr145a, htr3410a, htr345a, htr4710c, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd14a, hd710b, htr147a, htr478a, htr5710a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd14a, hd810b, htr145a, htr457a, htr578a, htr7810a]
          ·
            linarith only [hlam, hd14a, hd78b, htr145a, htr3410a, htr345a, htr4810c, htr7810a]
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
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc124yx, hc789yx, htr012a, htr017a, htr145a, htr179a, htr457a, htr578a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hc124yx, hc7810yx, htr012a, htr017a, htr145a, htr1710a, htr457a, htr578a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc134yz, htr147b, htr179a, htr347a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                linarith only [hlam, hc134yz, htr147b, htr1710a, htr347a, htr4710a])
              obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd14a, hd78b, htr147a, htr479a, htr578a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc124yx, hc789zy, htr012a, htr018a, htr145a, htr189a, htr457a, htr579a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc134yz, htr148b, htr189a, htr348a, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                linarith only [hlam, hd14a, hd78b, htr147a, htr4710a, htr5710a, htr578a])
              obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc124yx, hc7910zy, htr012a, htr019a, htr145a, htr1910a, htr457a, htr5710a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd14a, hd89b, htr145a, htr457a, htr578a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd14a, hd910b, htr145a, htr457a, htr579a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd14a, hd79b, htr148a, htr489a, htr7910a, htr8910a]
              ·
                linarith only [hlam, hc178yz, htr189b, htr1910a, htr789a, htr8910a]
            ·
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd14a, hd79b, htr147a, htr478a, htr578a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              rcases m.htr 6 7 9 (by decide) (by decide) with
                ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
              ·
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hc567zy, htr047c, htr079a, htr478a, htr578a, htr679a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc567zy, htr378a, htr379a, htr578a, htr679a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                rcases m.htr 6 7 10 (by decide) (by decide) with
                  ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
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
                      linarith only [hlam, hc157yz, htr178b, htr1810a, htr378c, htr3810a, htr578a])
                    obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hd14a, hd58b, htr147a, htr478a, htr589a, htr789a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                      linarith only [hlam, hd13a, hd89b, htr138a, htr3810a, htr5810a, htr589a])
                    obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                    have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                      linarith only [hlam, hc124yx, hc8910zy, htr012a, htr019a, htr145a, htr1910a, htr458a, htr5810a])
                    obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hc567zy, htr169b, htr1910a, htr579a, htr679b, htr7910a])
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
                      linarith only [hlam, hc057yz, htr078b, htr089a, htr578a, htr789a])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc157yz, htr178b, htr189a, htr578a, htr789a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      linarith only [hlam, hc124yx, hc8910xy, htr012a, htr018a, htr147a, htr189a, htr478a, htr7810a])
                    obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc057yz, htr078b, htr0810a, htr578a, htr7810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hd46b, hd89a, htr048c, htr0810a, htr1810a, htr189a, htr346a, htr348a])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                      linarith only [hlam, hc124yx, hc8910yz, htr012a, htr018a, htr145a, htr1810a, htr459a, htr5910a])
                    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                    have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                      linarith only [hlam, hc123yx, hc589zy, htr012a, htr018a, htr139a, htr189a, htr3910a, htr5910a])
                    obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                    have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                      linarith only [hlam, hc567zy, htr069b, htr0910a, htr379c, htr3910a, htr579a, htr679b])
                    obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd46b, hd89a, htr049c, htr0910a, htr346a, htr349a, htr8910a]
                    ·
                      linarith only [hlam, hd46b, hd910a, htr048c, htr089a, htr346a, htr348a, htr8910a]
                ·
                  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                    linarith only [hlam, htr067b, htr0710a, htr6710a])
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
                    linarith only [hlam, hd46b, hd710a, htr048c, htr0810a, htr167b, htr178b, htr1810a, htr346a, htr348a, htr6710a])
                  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hc124yx, hc8910yx, htr012a, htr018a, htr147a, htr1810a, htr478a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, hc057yz, htr078b, htr089a, htr578a, htr789a])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd46b, hd89a, htr049c, htr0910a, htr346a, htr349a, htr8910a]
                  ·
                    linarith only [hlam, hd46b, hd910a, htr048c, htr089a, htr346a, htr348a, htr8910a]
              ·
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, htr067b, htr079a, htr679a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, htr078b, htr079c, htr089b])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hd46b, hd79a, htr048c, htr089a, htr167b, htr178b, htr189a, htr346a, htr348a, htr679a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, htr137c, htr167b, htr379a, htr679a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  linarith only [hlam, hc124yx, hc8910xy, htr012a, htr018a, htr147a, htr189a, htr478a, htr7810a])
                obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, hc057yz, htr078b, htr0810a, htr578a, htr7810a])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hd46b, hd79a, htr048c, htr0810a, htr167b, htr178b, htr1810a, htr346a, htr348a, htr679a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                  linarith only [hlam, hc124yx, hc8910yz, htr012a, htr018a, htr145a, htr1810a, htr459a, htr5910a])
                obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                  linarith only [hlam, hc123yx, hc579zy, htr012a, htr017a, htr139a, htr167b, htr3910a, htr5910a, htr679a])
                obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd57b, hd89a, htr378a, htr379c, htr3910a, htr578a, htr8910a]
                ·
                  linarith only [hlam, hd46b, hd910a, htr048c, htr089a, htr346a, htr348a, htr8910a]
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
              linarith only [hlam, hd46b, hd89a, htr346a, htr347a, htr478a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hd46b, hd78a, htr346a, htr348a, htr489a, htr789a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc124yx, hc578zy, htr012a, htr017a, htr148a, htr178a, htr489a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc124yx, hc789yz, htr012a, htr017a, htr145a, htr179a, htr458a, htr589a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
              linarith only [hlam, hc124yx, hc8910yx, htr012a, htr018a, htr145a, htr1810a, htr458a, htr589a])
            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hd46b, hd78a, htr178a, htr179a, htr346a, htr347c, htr379a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
              linarith only [hlam, hc128yx, hc789xy, htr012a, htr017a, htr178a, htr1810a, htr378c, htr379a, htr3810a])
            obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
            have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
              linarith only [hlam, hc123yx, hc578zy, htr012a, htr017a, htr138a, htr178a, htr3810a, htr5810a])
            obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
              linarith only [hlam, hc124yx, hc8910zy, htr012a, htr019a, htr145a, htr1910a, htr458a, htr5810a])
            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hc789xy, htr178a, htr179b, htr1910a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hd14a, hd910b, htr145a, htr458a, htr589a, htr8910a]
            ·
              linarith only [hlam, hd78a, hd89b, htr178a, htr179a, htr7910a, htr8910a]

theorem shard_301 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr048c : m.d 0 8 < m.d 4 8)
    (htr049c : m.d 0 9 < m.d 4 9)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr147b : m.d 1 4 < m.d 1 7)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr148b : m.d 1 4 < m.d 1 8)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr149c : m.d 1 9 < m.d 4 9)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr158a : m.d 1 5 + lam ≤ m.d 5 8)
    (htr159a : m.d 1 5 + lam ≤ m.d 5 9)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    : False :=
  proof_shard_301 m htr012a htr013a htr014a htr016a htr016b htr047c htr048c htr049c htr126a htr137a htr137c htr138a htr139a htr145a htr145b htr147a htr147b htr147c htr148a htr148b htr148c htr149a htr149c htr157a htr158a htr159a htr345a htr346a

#print axioms shard_301
end Jsp404.NoSatElevenDBMTerminal
