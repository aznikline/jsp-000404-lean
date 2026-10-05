import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_064 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr239b : m.d 3 9 < m.d 2 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hd23b, hd34a, htr123a, htr124a, htr245a, htr345a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc234yx, htr014c, htr045a, htr123a, htr124c, htr245a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc234yx, htr123a, htr124c, htr145a, htr245a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  rcases m.htr 1 4 6 (by decide) (by decide) with
    ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr014c, htr046a, htr146a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    rcases m.htr 1 4 7 (by decide) (by decide) with
      ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
    ·
      rcases m.htr 1 4 8 (by decide) (by decide) with
        ⟨htr148a, htr148b, htr148c, _, _⟩ | ⟨htr148a, htr148b, htr148c, _, _⟩
      ·
        rcases m.htr 1 4 9 (by decide) (by decide) with
          ⟨htr149a, htr149b, htr149c, _, _⟩ | ⟨htr149a, htr149b, htr149c, _, _⟩
        ·
          rcases m.htr 1 4 10 (by decide) (by decide) with
            ⟨htr1410a, htr1410b, htr1410c, _, _⟩ | ⟨htr1410a, htr1410b, htr1410c, _, _⟩
          ·
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, htr045c, htr056a, htr456a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd01a, hd67b, htr014a, htr145a, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd01a, hd68b, htr014a, htr145a, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd01a, hd56b, htr014a, htr146a, htr468a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd01a, hd78b, htr014a, htr145a, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd01a, hd79b, htr014a, htr145a, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                rcases m.htr 4 5 8 (by decide) (by decide) with
                  ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                ·
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd01a, hd89b, htr014a, htr145a, htr458a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 3 6 7 (by decide) (by decide) with
                    ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
                  ·
                    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                      linarith only [hlam, hd23b, hd36a, htr123a, htr126a, htr267a, htr367a])
                    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                      linarith only [hlam, hc236yx, htr016c, htr067a, htr123a, htr126c, htr267a])
                    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                    have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                      linarith only [hlam, hc569yx, htr056b, htr059a, htr067a, htr567a])
                    obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                    have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr159a, htr159b, htr159c, _, _⟩
                      linarith only [hlam, hc235yx, htr025b, htr059a, htr123a, htr125c, htr159a])
                    obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
                    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
                      linarith only [hlam, hd01a, hd56b, htr015a, htr159a, htr456a, htr459a])
                    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
                    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                      linarith only [hlam, hd01a, hd910b, htr014a, htr145a, htr459a, htr5910a])
                    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc356yz, htr237b, htr278a, htr367b, htr567a, htr678a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hc356yz, htr367a, htr567c, htr579a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd23b, hd89a, htr123a, htr127a, htr278a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hd23b, hd78a, htr123a, htr128a, htr289a, htr789a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc238yx, htr123a, htr128c, htr189a, htr289a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd01a, hd56b, htr018a, htr189a, htr568a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, hc056yz, htr068a, htr568c, htr589a, htr689a])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                      linarith only [hlam, hc568zy, htr068a, htr069a, htr589a, htr689c])
                    obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hd56b, hd910a, htr067a, htr069a, htr567a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a]
                    ·
                      linarith only [hlam, hc578zy, htr589a, htr679b, htr6910a, htr789b, htr8910a]
                  ·
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd23b, hd78a, htr123a, htr126a, htr236b, htr367a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hc567zy, htr236b, htr268a, htr367a, htr578a, htr678c])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd23b, hd89a, htr123a, htr126a, htr268a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a]
                    ·
                      linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a]
                ·
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, hd01a, hd56b, htr015a, htr158a, htr456a, htr458a])
                  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hc235yx, htr025b, htr058a, htr123a, htr125c, htr158a])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, hc568yx, htr056b, htr058a, htr067a, htr567a])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                    linarith only [hlam, hc236yx, htr016c, htr067a, htr123a, htr126c, htr267a])
                  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hc567zy, htr457a, htr458a, htr578b, htr678a]
                  ·
                    linarith only [hlam, hd23b, hd78a, htr123a, htr126a, htr267a, htr678a]
              ·
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hd01a, hd56b, htr015a, htr157a, htr456a, htr457a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc235yx, htr025b, htr057a, htr123a, htr125c, htr157a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hc235yx, htr123a, htr125c, htr157a, htr257a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hc236yx, htr016c, htr068a, htr123a, htr126c, htr268a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd23b, hd78a, htr123a, htr125a, htr257a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd23b, hd89a, htr123a, htr126a, htr268a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hd23b, hd68a, htr123a, htr128a, htr289a, htr689a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc238yx, htr123a, htr128c, htr189a, htr289a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd01a, hd89b, htr014a, htr147a, htr478a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hd01a, hd78b, htr014a, htr148a, htr489a, htr789a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc567yx, htr018c, htr057a, htr058b, htr189a, htr456c, htr468c, htr489a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                rcases m.htr 4 5 8 (by decide) (by decide) with
                  ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                ·
                  linarith only [hlam, htr045c, htr058a, htr458a]
                ·
                  linarith only [hlam, hc238yx, hc567yx, htr123a, htr125a, htr257a, htr289a, htr456a, htr458c, htr489a]
            ·
              rcases m.htr 3 5 6 (by decide) (by decide) with
                ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
              ·
                have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                  linarith only [hlam, hd23b, hd35a, htr123a, htr125a, htr256a, htr356a])
                obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc235yx, htr015c, htr056a, htr123a, htr125c, htr256a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                  linarith only [hlam, hc235yx, htr123a, htr125c, htr156a, htr256a])
                obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
                have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                  linarith only [hlam, hd01a, hd57b, htr015a, htr156a, htr456a, htr457a])
                obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                  linarith only [hlam, hd01a, hd58b, htr015a, htr156a, htr456a, htr458a])
                obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
                have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr459a, htr459b, htr459c, _, _⟩
                  linarith only [hlam, hd01a, hd59b, htr015a, htr156a, htr456a, htr459a])
                obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
                rcases m.htr 3 5 7 (by decide) (by decide) with
                  ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hc345yz, htr056a, htr057a, htr357a, htr456a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hc345yz, htr156a, htr157a, htr357a, htr456a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  rcases m.htr 3 5 8 (by decide) (by decide) with
                    ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
                  ·
                    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                      linarith only [hlam, hc345yz, htr156a, htr158a, htr358a, htr456a])
                    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                    rcases m.htr 3 5 9 (by decide) (by decide) with
                      ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
                    ·
                      have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr159a, htr159b, htr159c, _, _⟩
                        linarith only [hlam, hc345yz, htr156a, htr159a, htr359a, htr456a])
                      obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
                      rcases m.htr 3 5 10 (by decide) (by decide) with
                        ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                      ·
                        rcases m.htr 5 6 7 (by decide) (by decide) with
                          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                        ·
                          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                            linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a])
                          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hd01a, hd67b, htr015a, htr157a, htr578a, htr678a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                            linarith only [hlam, hc345yz, htr237b, htr278a, htr357b, htr457a, htr578a])
                          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hd01a, hd79b, htr015a, htr156a, htr567a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                            linarith only [hlam, hd01a, hd67b, htr015a, htr157a, htr579a, htr679a])
                          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                            linarith only [hlam, hc345yz, htr237b, htr279a, htr357b, htr457a, htr579a])
                          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hd23b, hd89a, htr123a, htr127a, htr278a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                            linarith only [hlam, hd23b, hd78a, htr123a, htr128a, htr289a, htr789a])
                          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc345yz, htr238b, htr289a, htr358b, htr458a, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                            linarith only [hlam, hd23b, hd910a, htr123a, htr127a, htr279a, htr7910a])
                          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                            linarith only [hlam, hd23b, hd79a, htr123a, htr129a, htr2910a, htr7910a])
                          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                            linarith only [hlam, hc345yz, htr239b, htr2910a, htr359b, htr459a, htr5910a])
                          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd01a, hd910b, htr015a, htr158a, htr589a, htr8910a]
                          ·
                            linarith only [hlam, hd01a, hd89b, htr015a, htr159a, htr5910a, htr8910a]
                        ·
                          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                            linarith only [hlam, hc345yz, htr236b, htr267a, htr356b, htr456a, htr567a])
                          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                            linarith only [hlam, hd23b, hd78a, htr123a, htr126a, htr267a, htr678a])
                          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                            linarith only [hlam, hd23b, hd67a, htr123a, htr127a, htr278a, htr678a])
                          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hc345yz, htr237b, htr278a, htr357b, htr457a, htr578a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                            linarith only [hlam, hc345yz, htr357a, htr457c, htr478a, htr578a])
                          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hd23b, hd79a, htr123a, htr126a, htr267a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                            linarith only [hlam, hd23b, hd67a, htr123a, htr127a, htr279a, htr679a])
                          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                            linarith only [hlam, hc237yx, htr123a, htr127c, htr179a, htr279a])
                          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                            linarith only [hlam, hd01a, hd78b, htr017a, htr179a, htr478a, htr479a])
                          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hd01a, hd89b, htr015a, htr157a, htr578a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hd01a, hd78b, htr015a, htr158a, htr589a, htr789a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                            linarith only [hlam, hc345yz, htr238b, htr289a, htr358b, htr458a, htr589a])
                          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                            linarith only [hlam, hd01a, hd910b, htr014a, htr147a, htr479a, htr7910a])
                          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                            linarith only [hlam, hd01a, hd79b, htr015a, htr159a, htr5910a, htr7910a])
                          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                            linarith only [hlam, hc345yz, htr239b, htr2910a, htr359b, htr459a, htr5910a])
                          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd23b, hd89a, htr123a, htr129a, htr2910a, htr8910a]
                          ·
                            linarith only [hlam, hd23b, hd910a, htr123a, htr128a, htr289a, htr8910a]
                      ·
                        have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                          linarith only [hlam, htr035b, htr0510a, htr3510a])
                        obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                        have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                          linarith only [hlam, htr0510c, htr056b, htr0610b])
                        obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                          linarith only [hlam, htr0510c, htr057b, htr0710b])
                        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                        have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                          linarith only [hlam, hc237yx, htr017c, htr0710a, htr123a, htr127c, htr2710a])
                        obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                        have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                          linarith only [hlam, htr056c, htr0610a, htr5610a])
                        obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc6710yx, htr235b, htr256a, htr3510a, htr5610b, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                          linarith only [hlam, hc345yz, htr236b, htr267a, htr356b, htr456a, htr567a])
                        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                        rcases m.htr 6 7 10 (by decide) (by decide) with
                          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                        ·
                          linarith only [hlam, hd23b, hd67a, htr123a, htr127a, htr2710a, htr6710a]
                        ·
                          linarith only [hlam, hd23b, hd710a, htr123a, htr126a, htr267a, htr6710a]
                    ·
                      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                        linarith only [hlam, htr035b, htr059a, htr359a])
                      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                        linarith only [hlam, htr056b, htr059c, htr069b])
                      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, htr057b, htr059c, htr079b])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, hc237yx, htr017c, htr079a, htr123a, htr127c, htr279a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, htr056c, htr069a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc679yx, htr235b, htr256a, htr359a, htr567a, htr569b])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                        linarith only [hlam, hc345yz, htr236b, htr267a, htr356b, htr456a, htr567a])
                      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                      rcases m.htr 6 7 9 (by decide) (by decide) with
                        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                      ·
                        linarith only [hlam, hd23b, hd67a, htr123a, htr127a, htr279a, htr679a]
                      ·
                        linarith only [hlam, hd23b, hd79a, htr123a, htr126a, htr267a, htr679a]
                  ·
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, htr035b, htr058a, htr358a])
                    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, htr056b, htr058c, htr068b])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, htr057b, htr058c, htr078b])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc237yx, htr017c, htr078a, htr123a, htr127c, htr278a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, htr056c, htr068a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hc678yx, htr235b, htr256a, htr358a, htr567a, htr568b])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                      linarith only [hlam, hc345yz, htr236b, htr267a, htr356b, htr456a, htr567a])
                    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd23b, hd67a, htr123a, htr127a, htr278a, htr678a]
                    ·
                      linarith only [hlam, hd23b, hd78a, htr123a, htr126a, htr267a, htr678a]
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, htr035b, htr057a, htr357a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, htr056b, htr057c, htr067b])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, htr056c, htr067a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hc678xy, htr235b, htr256a, htr357a, htr567b, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, hc345yz, htr236b, htr268a, htr356b, htr456a, htr568a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                    linarith only [hlam, hc679xy, htr235b, htr256a, htr357a, htr567b, htr569a])
                  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                    linarith only [hlam, hc345yz, htr236b, htr269a, htr356b, htr456a, htr569a])
                  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                    linarith only [hlam, hc6710xy, htr235b, htr256a, htr357a, htr5610a, htr567b])
                  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                    linarith only [hlam, hc345yz, htr236b, htr2610a, htr356b, htr456a, htr5610a])
                  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd23b, hd78a, htr123a, htr125a, htr235b, htr357a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, hc567yx, htr056a, htr057c, htr078a, htr578a])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd23b, hd79a, htr123a, htr125a, htr235b, htr357a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, hc567yx, htr056a, htr057c, htr079a, htr579a])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, htr567b, htr578a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, htr567b, htr579a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd23b, hd89a, htr123a, htr126a, htr268a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hd23b, hd68a, htr123a, htr128a, htr289a, htr689a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hd23b, hd910a, htr123a, htr126a, htr269a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hd01a, hd89b, htr014a, htr147a, htr478a, htr789a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hc237yx, hc679yz, htr027b, htr078a, htr123a, htr126a, htr269a, htr478a, htr479a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hc467zy, htr479a, htr679b, htr6910a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc237yx, hc6910yz, htr027b, htr078a, htr123a, htr126a, htr2610a, htr789a, htr8910a]
                    ·
                      linarith only [hlam, hc237yx, hc689yz, htr027b, htr079a, htr123a, htr126a, htr269a, htr7910a, htr8910a]
                  ·
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hc237yx, hc678yz, htr027b, htr079a, htr123a, htr126a, htr268a, htr478a, htr479a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hd01a, hd910b, htr014a, htr147a, htr479a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc238yx, hc679yz, htr123a, htr126a, htr269a, htr289a, htr7910a, htr8910a]
                    ·
                      linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
              ·
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd23b, hd67a, htr123a, htr125a, htr235b, htr356a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr267a, htr567a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc236yx, htr123a, htr126c, htr167a, htr267a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd23b, hd68a, htr123a, htr125a, htr235b, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr268a, htr568a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc236yx, htr123a, htr126c, htr168a, htr268a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hd23b, hd69a, htr123a, htr125a, htr235b, htr356a, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                  linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr269a, htr569a])
                obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                  linarith only [hlam, hc236yx, htr123a, htr126c, htr169a, htr269a])
                obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                rcases m.htr 4 6 7 (by decide) (by decide) with
                  ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                ·
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr467a, htr468a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                    linarith only [hlam, hd01a, hd67b, htr016a, htr169a, htr467a, htr469a])
                  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd01a, hd79b, htr014a, htr146a, htr467a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd01a, hd89b, htr014a, htr146a, htr468a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hd01a, hd910b, htr014a, htr146a, htr469a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 3 5 7 (by decide) (by decide) with
                    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                  ·
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hd56a, hd67b, htr356a, htr357a, htr578a, htr678a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc567xy, htr237b, htr278a, htr356a, htr357b, htr578a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                      linarith only [hlam, hd56a, hd67b, htr356a, htr357a, htr579a, htr679a])
                    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, hc567xy, htr237b, htr279a, htr356a, htr357b, htr579a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd23b, hd89a, htr123a, htr127a, htr278a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hd23b, hd910a, htr123a, htr127a, htr279a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
                    ·
                      linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
                  ·
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hd23b, hd78a, htr123a, htr125a, htr235b, htr357a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                      linarith only [hlam, hc567yz, htr235b, htr258a, htr357a, htr578c, htr678a])
                    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hd23b, hd89a, htr123a, htr125a, htr258a, htr589a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
                    ·
                      linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
                ·
                  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                    linarith only [hlam, hc456zy, htr235b, htr257a, htr356a, htr467a, htr567c])
                  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hd01a, hd68b, htr016a, htr167a, htr467a, htr468a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, hc456zy, htr235b, htr258a, htr356a, htr468a, htr568c])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd23b, hd78a, htr123a, htr125a, htr257a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd23b, hd89a, htr123a, htr125a, htr258a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd01a, hd89b, htr016a, htr167a, htr678a, htr789a]
                  ·
                    linarith only [hlam, hd01a, hd78b, htr016a, htr168a, htr689a, htr789a]
          ·
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, hc234yx, htr024b, htr0410a, htr123a, htr124c, htr1410a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, htr0410c, htr045b, htr0510b])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0410c, htr046b, htr0610b])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
              linarith only [hlam, hc234yx, htr123a, htr124c, htr1410a, htr2410a])
            obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
            have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
              linarith only [hlam, hc236yx, htr016c, htr0610a, htr123a, htr126c, htr2610a])
            obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
            have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
              linarith only [hlam, htr045c, htr0510a, htr4510a])
            obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hc5610yx, htr014c, htr0410a, htr145a, htr4510b, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc4510yx, htr2410a, htr245b, htr256a, htr456a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            rcases m.htr 5 6 10 (by decide) (by decide) with
              ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            ·
              linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr2610a, htr5610a]
            ·
              linarith only [hlam, hd23b, hd610a, htr123a, htr125a, htr256a, htr5610a]
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc234yx, htr024b, htr049a, htr123a, htr124c, htr149a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr045b, htr049c, htr059b])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr046b, htr049c, htr069b])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr249a, htr249b, htr249c, _, _⟩
            linarith only [hlam, hc234yx, htr123a, htr124c, htr149a, htr249a])
          obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
          have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr269a, htr269b, htr269c, _, _⟩
            linarith only [hlam, hc236yx, htr016c, htr069a, htr123a, htr126c, htr269a])
          obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, htr045c, htr059a, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr456a, htr456b, htr456c, _, _⟩
            linarith only [hlam, hc569yx, htr014c, htr049a, htr145a, htr456a, htr459b])
          obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc459yx, htr245b, htr249a, htr256a, htr456a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr269a, htr569a]
          ·
            linarith only [hlam, hd23b, hd69a, htr123a, htr125a, htr256a, htr569a]
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc234yx, htr024b, htr048a, htr123a, htr124c, htr148a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr045b, htr048c, htr058b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr046b, htr048c, htr068b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc234yx, htr123a, htr124c, htr148a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc236yx, htr016c, htr068a, htr123a, htr126c, htr268a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, htr045c, htr058a, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr456a, htr456b, htr456c, _, _⟩
          linarith only [hlam, hc568yx, htr014c, htr048a, htr145a, htr456a, htr458b])
        obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc458yx, htr245b, htr248a, htr256a, htr456a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr268a, htr568a]
        ·
          linarith only [hlam, hd23b, hd68a, htr123a, htr125a, htr256a, htr568a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc234yx, htr024b, htr047a, htr123a, htr124c, htr147a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr045b, htr047c, htr057b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr046b, htr047c, htr067b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc234yx, htr123a, htr124c, htr147a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc236yx, htr016c, htr067a, htr123a, htr126c, htr267a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, htr045c, htr057a, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc567yx, htr014c, htr047a, htr145a, htr456a, htr457b])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc457yx, htr245b, htr247a, htr256a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr267a, htr567a]
      ·
        linarith only [hlam, hd23b, hd67a, htr123a, htr125a, htr256a, htr567a]
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc234yx, htr024b, htr046a, htr123a, htr124c, htr146a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, htr045b, htr046c, htr056b])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hc234yx, htr123a, htr124c, htr146a, htr246a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, htr045c, htr056a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567xy, htr014c, htr046a, htr145a, htr456b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc456yx, htr245b, htr246a, htr257a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568xy, htr014c, htr046a, htr145a, htr456b, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc456yx, htr245b, htr246a, htr258a, htr458a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hc569xy, htr014c, htr046a, htr145a, htr456b, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr259a, htr259b, htr259c, _, _⟩
      linarith only [hlam, hc456yx, htr245b, htr246a, htr259a, htr459a])
    obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
    have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
      linarith only [hlam, hc5610xy, htr014c, htr046a, htr145a, htr4510a, htr456b])
    obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
    have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
      linarith only [hlam, hc456yx, htr245b, htr246a, htr2510a, htr4510a])
    obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd23b, hd67a, htr123a, htr124a, htr246a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc456yx, htr016c, htr067a, htr145a, htr146c, htr467a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd23b, hd78a, htr123a, htr125a, htr257a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd23b, hd57a, htr123a, htr127a, htr278a, htr578a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd23b, hd79a, htr123a, htr125a, htr257a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd23b, hd57a, htr123a, htr127a, htr279a, htr579a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd23b, hd89a, htr123a, htr125a, htr258a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hd23b, hd58a, htr123a, htr128a, htr289a, htr589a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      linarith only [hlam, hd23b, hd910a, htr123a, htr125a, htr259a, htr5910a])
    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc237yx, hc578yz, htr123a, htr125a, htr258a, htr279a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc236yx, hc589yz, htr026b, htr067a, htr123a, htr125a, htr259a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc236yx, hc5910yz, htr026b, htr067a, htr123a, htr125a, htr2510a, htr679a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc238yx, hc579yz, htr123a, htr125a, htr259a, htr289a, htr7910a, htr8910a]
      ·
        linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]
    ·
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc237yx, hc579yz, htr123a, htr125a, htr259a, htr278a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc237yx, hc5910yz, htr123a, htr125a, htr2510a, htr278a, htr789a, htr8910a]
      ·
        linarith only [hlam, hc237yx, hc589yz, htr123a, htr125a, htr259a, htr279a, htr7910a, htr8910a]

theorem shard_064 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr239b : m.d 3 9 < m.d 2 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_064 m htr014a htr014c htr015a htr015c htr016a htr016c htr017a htr017c htr018a htr018c htr024b htr025b htr026b htr027b htr035b htr123a htr124a htr124c htr125a htr125c htr126a htr126c htr127a htr127c htr128a htr128c htr129a htr235b htr236b htr237b htr238b htr239b htr345a

#print axioms shard_064
end Jsp404.NoSatElevenDBMTerminal
