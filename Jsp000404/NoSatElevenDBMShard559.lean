import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_559 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127b : m.d 1 2 < m.d 1 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  have hd59a := (m.hrange 5 9 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
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
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hd23a, hd34b, htr123a, htr124a, htr245a, htr345a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc234xy, htr014b, htr045a, htr123a, htr124b, htr245a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc234xy, htr123a, htr124b, htr145a, htr245a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  rcases m.htr 1 4 6 (by decide) (by decide) with
    ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc234xy, htr024c, htr046a, htr123a, htr124b, htr146a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, htr045c, htr046b, htr056c])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hc234xy, htr123a, htr124b, htr146a, htr246a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, htr045b, htr056a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567yx, htr014b, htr046a, htr145a, htr456c, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc456xy, htr245c, htr246a, htr257a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568yx, htr014b, htr046a, htr145a, htr456c, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc456xy, htr245c, htr246a, htr258a, htr458a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hc569yx, htr014b, htr046a, htr145a, htr456c, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr259a, htr259b, htr259c, _, _⟩
      linarith only [hlam, hc456xy, htr245c, htr246a, htr259a, htr459a])
    obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
    have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
      linarith only [hlam, hc5610yx, htr014b, htr046a, htr145a, htr4510a, htr456c])
    obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
    have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
      linarith only [hlam, hc456xy, htr245c, htr246a, htr2510a, htr4510a])
    obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd23a, hd67b, htr123a, htr124a, htr246a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc456xy, htr016b, htr067a, htr145a, htr146b, htr467a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd23a, hd78b, htr123a, htr125a, htr257a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd23a, hd57b, htr123a, htr127a, htr278a, htr578a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd23a, hd79b, htr123a, htr125a, htr257a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd23a, hd57b, htr123a, htr127a, htr279a, htr579a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd23a, hd89b, htr123a, htr125a, htr258a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hd23a, hd58b, htr123a, htr128a, htr289a, htr589a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      linarith only [hlam, hd23a, hd910b, htr123a, htr125a, htr259a, htr5910a])
    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc237xy, hc579zy, htr123a, htr125a, htr259a, htr278a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc567zy, htr579c, htr5910a, htr679a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc237xy, hc589zy, htr123a, htr125a, htr259a, htr279a, htr7910a, htr8910a]
      ·
        linarith only [hlam, hc237xy, hc5910zy, htr123a, htr125a, htr2510a, htr278a, htr789a, htr8910a]
    ·
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc237xy, hc578zy, htr123a, htr125a, htr258a, htr279a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc236xy, hc589zy, htr026c, htr067a, htr123a, htr125a, htr259a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc236xy, hc5910zy, htr026c, htr067a, htr123a, htr125a, htr2510a, htr679a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a]
      ·
        linarith only [hlam, hc238xy, hc579zy, htr123a, htr125a, htr259a, htr289a, htr7910a, htr8910a]
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr014b, htr046a, htr146a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    rcases m.htr 1 4 7 (by decide) (by decide) with
      ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc234xy, htr024c, htr047a, htr123a, htr124b, htr147a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr045c, htr047b, htr057c])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr046c, htr047b, htr067c])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc234xy, htr123a, htr124b, htr147a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc236xy, htr016b, htr067a, htr123a, htr126b, htr267a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, htr045b, htr057a, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc567xy, htr014b, htr047a, htr145a, htr456a, htr457c])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc457xy, htr245c, htr247a, htr256a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        linarith only [hlam, hd23a, hd67b, htr123a, htr125a, htr256a, htr567a]
      ·
        linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr267a, htr567a]
    ·
      rcases m.htr 1 4 8 (by decide) (by decide) with
        ⟨htr148a, htr148b, htr148c, _, _⟩ | ⟨htr148a, htr148b, htr148c, _, _⟩
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc234xy, htr024c, htr048a, htr123a, htr124b, htr148a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr045c, htr048b, htr058c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr046c, htr048b, htr068c])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc234xy, htr123a, htr124b, htr148a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc236xy, htr016b, htr068a, htr123a, htr126b, htr268a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, htr045b, htr058a, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr456a, htr456b, htr456c, _, _⟩
          linarith only [hlam, hc568xy, htr014b, htr048a, htr145a, htr456a, htr458c])
        obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc458xy, htr245c, htr248a, htr256a, htr456a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd68b, htr123a, htr125a, htr256a, htr568a]
        ·
          linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr268a, htr568a]
      ·
        rcases m.htr 1 4 9 (by decide) (by decide) with
          ⟨htr149a, htr149b, htr149c, _, _⟩ | ⟨htr149a, htr149b, htr149c, _, _⟩
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc234xy, htr024c, htr049a, htr123a, htr124b, htr149a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr045c, htr049b, htr059c])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr046c, htr049b, htr069c])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr249a, htr249b, htr249c, _, _⟩
            linarith only [hlam, hc234xy, htr123a, htr124b, htr149a, htr249a])
          obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
          have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr269a, htr269b, htr269c, _, _⟩
            linarith only [hlam, hc236xy, htr016b, htr069a, htr123a, htr126b, htr269a])
          obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, htr045b, htr059a, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr456a, htr456b, htr456c, _, _⟩
            linarith only [hlam, hc569xy, htr014b, htr049a, htr145a, htr456a, htr459c])
          obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc459xy, htr245c, htr249a, htr256a, htr456a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd69b, htr123a, htr125a, htr256a, htr569a]
          ·
            linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr269a, htr569a]
        ·
          rcases m.htr 1 4 10 (by decide) (by decide) with
            ⟨htr1410a, htr1410b, htr1410c, _, _⟩ | ⟨htr1410a, htr1410b, htr1410c, _, _⟩
          ·
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, hc234xy, htr024c, htr0410a, htr123a, htr124b, htr1410a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, htr0410b, htr045c, htr0510c])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0410b, htr046c, htr0610c])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
              linarith only [hlam, hc234xy, htr123a, htr124b, htr1410a, htr2410a])
            obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
            have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
              linarith only [hlam, hc236xy, htr016b, htr0610a, htr123a, htr126b, htr2610a])
            obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
            have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
              linarith only [hlam, htr045b, htr0510a, htr4510a])
            obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hc5610xy, htr014b, htr0410a, htr145a, htr4510c, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc4510xy, htr2410a, htr245c, htr256a, htr456a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            rcases m.htr 5 6 10 (by decide) (by decide) with
              ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd610b, htr123a, htr125a, htr256a, htr5610a]
            ·
              linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr2610a, htr5610a]
          ·
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              rcases m.htr 3 5 6 (by decide) (by decide) with
                ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
              ·
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd23a, hd67b, htr123a, htr125a, htr235c, htr356a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr267a, htr567a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc236xy, htr123a, htr126b, htr167a, htr267a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd23a, hd68b, htr123a, htr125a, htr235c, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr268a, htr568a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc236xy, htr123a, htr126b, htr168a, htr268a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hd23a, hd69b, htr123a, htr125a, htr235c, htr356a, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                  linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr269a, htr569a])
                obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                  linarith only [hlam, hc236xy, htr123a, htr126b, htr169a, htr269a])
                obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                rcases m.htr 4 6 7 (by decide) (by decide) with
                  ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                ·
                  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                    linarith only [hlam, hc456yz, htr235c, htr257a, htr356a, htr467a, htr567b])
                  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hd01b, hd68a, htr016a, htr167a, htr467a, htr468a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, hc456yz, htr235c, htr258a, htr356a, htr468a, htr568b])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd23a, hd78b, htr123a, htr125a, htr257a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd23a, hd89b, htr123a, htr125a, htr258a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc456yz, htr468a, htr568c, htr589a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd01b, hd78a, htr016a, htr168a, htr689a, htr789a]
                  ·
                    linarith only [hlam, hd01b, hd89a, htr016a, htr167a, htr678a, htr789a]
                ·
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hd01b, hd67a, htr016a, htr168a, htr467a, htr468a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                    linarith only [hlam, hd01b, hd67a, htr016a, htr169a, htr467a, htr469a])
                  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd01b, hd79a, htr014a, htr146a, htr467a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd01b, hd89a, htr014a, htr146a, htr468a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hd01b, hd910a, htr014a, htr146a, htr469a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 3 5 7 (by decide) (by decide) with
                    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                  ·
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hd23a, hd78b, htr123a, htr125a, htr235c, htr357a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                      linarith only [hlam, hc567zy, htr235c, htr258a, htr357a, htr578b, htr678a])
                    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hd23a, hd89b, htr123a, htr125a, htr258a, htr589a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a]
                    ·
                      linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a]
                  ·
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hd56b, hd67a, htr356a, htr357a, htr578a, htr678a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc567yx, htr237c, htr278a, htr356a, htr357c, htr578a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                      linarith only [hlam, hd56b, hd67a, htr356a, htr357a, htr579a, htr679a])
                    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, hc567yx, htr237c, htr279a, htr356a, htr357c, htr579a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd23a, hd89b, htr123a, htr127a, htr278a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hd23a, hd910b, htr123a, htr127a, htr279a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
                    ·
                      linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
              ·
                have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                  linarith only [hlam, hd23a, hd35b, htr123a, htr125a, htr256a, htr356a])
                obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc235xy, htr015b, htr056a, htr123a, htr125b, htr256a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                  linarith only [hlam, hc235xy, htr123a, htr125b, htr156a, htr256a])
                obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
                have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                  linarith only [hlam, hd01b, hd57a, htr015a, htr156a, htr456a, htr457a])
                obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                  linarith only [hlam, hd01b, hd58a, htr015a, htr156a, htr456a, htr458a])
                obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
                have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr459a, htr459b, htr459c, _, _⟩
                  linarith only [hlam, hd01b, hd59a, htr015a, htr156a, htr456a, htr459a])
                obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
                rcases m.htr 3 5 7 (by decide) (by decide) with
                  ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, htr035c, htr057a, htr357a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, htr056c, htr057b, htr067c])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, htr056b, htr067a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hc678yx, htr235c, htr256a, htr357a, htr567c, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, hc345zy, htr236c, htr268a, htr356c, htr456a, htr568a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                    linarith only [hlam, hc679yx, htr235c, htr256a, htr357a, htr567c, htr569a])
                  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                    linarith only [hlam, hc345zy, htr236c, htr269a, htr356c, htr456a, htr569a])
                  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                    linarith only [hlam, hc6710yx, htr235c, htr256a, htr357a, htr5610a, htr567c])
                  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                    linarith only [hlam, hc345zy, htr236c, htr2610a, htr356c, htr456a, htr5610a])
                  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd23a, hd78b, htr123a, htr125a, htr235c, htr357a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, hc567xy, htr056a, htr057b, htr078a, htr578a])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd23a, hd79b, htr123a, htr125a, htr235c, htr357a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, hc567xy, htr056a, htr057b, htr079a, htr579a])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, htr567c, htr578a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, htr567c, htr579a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd23a, hd89b, htr123a, htr126a, htr268a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hd23a, hd68b, htr123a, htr128a, htr289a, htr689a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hd23a, hd910b, htr123a, htr126a, htr269a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hc237xy, hc678zy, htr027c, htr079a, htr123a, htr126a, htr268a, htr478a, htr479a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hd01b, hd910a, htr014a, htr147a, htr479a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
                    ·
                      linarith only [hlam, hc238xy, hc679zy, htr123a, htr126a, htr269a, htr289a, htr7910a, htr8910a]
                  ·
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hd01b, hd89a, htr014a, htr147a, htr478a, htr789a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hc237xy, hc679zy, htr027c, htr078a, htr123a, htr126a, htr269a, htr478a, htr479a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc237xy, hc689zy, htr027c, htr079a, htr123a, htr126a, htr269a, htr7910a, htr8910a]
                    ·
                      linarith only [hlam, hc237xy, hc6910zy, htr027c, htr078a, htr123a, htr126a, htr2610a, htr789a, htr8910a]
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hc345zy, htr056a, htr057a, htr357a, htr456a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hc345zy, htr156a, htr157a, htr357a, htr456a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  rcases m.htr 3 5 8 (by decide) (by decide) with
                    ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
                  ·
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, htr035c, htr058a, htr358a])
                    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, htr056c, htr058b, htr068c])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, htr057c, htr058b, htr078c])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc237xy, htr017b, htr078a, htr123a, htr127b, htr278a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, htr056b, htr068a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hc678xy, htr235c, htr256a, htr358a, htr567a, htr568c])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                      linarith only [hlam, hc345zy, htr236c, htr267a, htr356c, htr456a, htr567a])
                    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd23a, hd78b, htr123a, htr126a, htr267a, htr678a]
                    ·
                      linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr278a, htr678a]
                  ·
                    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                      linarith only [hlam, hc345zy, htr156a, htr158a, htr358a, htr456a])
                    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                    rcases m.htr 3 5 9 (by decide) (by decide) with
                      ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
                    ·
                      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                        linarith only [hlam, htr035c, htr059a, htr359a])
                      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                        linarith only [hlam, htr056c, htr059b, htr069c])
                      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, htr057c, htr059b, htr079c])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, hc237xy, htr017b, htr079a, htr123a, htr127b, htr279a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, htr056b, htr069a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc679xy, htr235c, htr256a, htr359a, htr567a, htr569c])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                        linarith only [hlam, hc345zy, htr236c, htr267a, htr356c, htr456a, htr567a])
                      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                      rcases m.htr 6 7 9 (by decide) (by decide) with
                        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                      ·
                        linarith only [hlam, hd23a, hd79b, htr123a, htr126a, htr267a, htr679a]
                      ·
                        linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr279a, htr679a]
                    ·
                      have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr159a, htr159b, htr159c, _, _⟩
                        linarith only [hlam, hc345zy, htr156a, htr159a, htr359a, htr456a])
                      obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
                      rcases m.htr 3 5 10 (by decide) (by decide) with
                        ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                      ·
                        have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                          linarith only [hlam, htr035c, htr0510a, htr3510a])
                        obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                        have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                          linarith only [hlam, htr0510b, htr056c, htr0610c])
                        obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                          linarith only [hlam, htr0510b, htr057c, htr0710c])
                        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                        have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                          linarith only [hlam, hc237xy, htr017b, htr0710a, htr123a, htr127b, htr2710a])
                        obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                        have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                          linarith only [hlam, htr056b, htr0610a, htr5610a])
                        obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc6710xy, htr235c, htr256a, htr3510a, htr5610c, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                          linarith only [hlam, hc345zy, htr236c, htr267a, htr356c, htr456a, htr567a])
                        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                        rcases m.htr 6 7 10 (by decide) (by decide) with
                          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                        ·
                          linarith only [hlam, hd23a, hd710b, htr123a, htr126a, htr267a, htr6710a]
                        ·
                          linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr2710a, htr6710a]
                      ·
                        rcases m.htr 5 6 7 (by decide) (by decide) with
                          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                        ·
                          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                            linarith only [hlam, hc345zy, htr236c, htr267a, htr356c, htr456a, htr567a])
                          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                            linarith only [hlam, hd23a, hd78b, htr123a, htr126a, htr267a, htr678a])
                          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                            linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr278a, htr678a])
                          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hc345zy, htr237c, htr278a, htr357c, htr457a, htr578a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                            linarith only [hlam, hc345zy, htr357a, htr457b, htr478a, htr578a])
                          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hd23a, hd79b, htr123a, htr126a, htr267a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                            linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr279a, htr679a])
                          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                            linarith only [hlam, hc237xy, htr123a, htr127b, htr179a, htr279a])
                          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                            linarith only [hlam, hd01b, hd78a, htr017a, htr179a, htr478a, htr479a])
                          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hd01b, hd89a, htr015a, htr157a, htr578a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hd01b, hd78a, htr015a, htr158a, htr589a, htr789a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                            linarith only [hlam, hc345zy, htr238c, htr289a, htr358c, htr458a, htr589a])
                          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                            linarith only [hlam, hd01b, hd910a, htr014a, htr147a, htr479a, htr7910a])
                          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                            linarith only [hlam, hd01b, hd79a, htr015a, htr159a, htr5910a, htr7910a])
                          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                            linarith only [hlam, hc345zy, htr239c, htr2910a, htr359c, htr459a, htr5910a])
                          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd23a, hd910b, htr123a, htr128a, htr289a, htr8910a]
                          ·
                            linarith only [hlam, hd23a, hd89b, htr123a, htr129a, htr2910a, htr8910a]
                        ·
                          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                            linarith only [hlam, hd01b, hd78a, htr015a, htr156a, htr567a, htr678a])
                          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hd01b, hd67a, htr015a, htr157a, htr578a, htr678a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                            linarith only [hlam, hc345zy, htr237c, htr278a, htr357c, htr457a, htr578a])
                          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hd01b, hd79a, htr015a, htr156a, htr567a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                            linarith only [hlam, hd01b, hd67a, htr015a, htr157a, htr579a, htr679a])
                          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                            linarith only [hlam, hc345zy, htr237c, htr279a, htr357c, htr457a, htr579a])
                          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hd23a, hd89b, htr123a, htr127a, htr278a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                            linarith only [hlam, hd23a, hd78b, htr123a, htr128a, htr289a, htr789a])
                          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc345zy, htr238c, htr289a, htr358c, htr458a, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                            linarith only [hlam, hd23a, hd910b, htr123a, htr127a, htr279a, htr7910a])
                          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                            linarith only [hlam, hd23a, hd79b, htr123a, htr129a, htr2910a, htr7910a])
                          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                            linarith only [hlam, hc345zy, htr239c, htr2910a, htr359c, htr459a, htr5910a])
                          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd01b, hd89a, htr015a, htr159a, htr5910a, htr8910a]
                          ·
                            linarith only [hlam, hd01b, hd910a, htr015a, htr158a, htr589a, htr8910a]
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, htr045b, htr056a, htr456a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd01b, hd67a, htr014a, htr145a, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd01b, hd68a, htr014a, htr145a, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd01b, hd56a, htr014a, htr146a, htr468a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hd01b, hd56a, htr015a, htr157a, htr456a, htr457a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc235xy, htr025c, htr057a, htr123a, htr125b, htr157a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc567xy, htr056c, htr057a, htr068a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hc235xy, htr123a, htr125b, htr157a, htr257a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hc236xy, htr016b, htr068a, htr123a, htr126b, htr268a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd23a, hd78b, htr123a, htr125a, htr257a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd23a, hd89b, htr123a, htr126a, htr268a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hd23a, hd68b, htr123a, htr128a, htr289a, htr689a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc238xy, htr123a, htr128b, htr189a, htr289a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd01b, hd89a, htr014a, htr147a, htr478a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hd01b, hd78a, htr014a, htr148a, htr489a, htr789a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc567xy, htr018b, htr057a, htr058c, htr189a, htr456b, htr468b, htr489a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                rcases m.htr 4 5 8 (by decide) (by decide) with
                  ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                ·
                  linarith only [hlam, hc238xy, hc567xy, htr123a, htr125a, htr257a, htr289a, htr456a, htr458b, htr489a]
                ·
                  linarith only [hlam, htr045b, htr058a, htr458a]
              ·
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd01b, hd78a, htr014a, htr145a, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd01b, hd79a, htr014a, htr145a, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                rcases m.htr 4 5 8 (by decide) (by decide) with
                  ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                ·
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, hd01b, hd56a, htr015a, htr158a, htr456a, htr458a])
                  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hc235xy, htr025c, htr058a, htr123a, htr125b, htr158a])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, hc568xy, htr056c, htr058a, htr067a, htr567a])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                    linarith only [hlam, hc236xy, htr016b, htr067a, htr123a, htr126b, htr267a])
                  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd23a, hd78b, htr123a, htr126a, htr267a, htr678a]
                  ·
                    linarith only [hlam, hc567yz, htr457a, htr458a, htr578c, htr678a]
                ·
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd01b, hd89a, htr014a, htr145a, htr458a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 3 6 7 (by decide) (by decide) with
                    ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
                  ·
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd23a, hd78b, htr123a, htr126a, htr236c, htr367a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hc567yz, htr236c, htr268a, htr367a, htr578a, htr678b])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd23a, hd89b, htr123a, htr126a, htr268a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
                    ·
                      linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
                  ·
                    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                      linarith only [hlam, hd23a, hd36b, htr123a, htr126a, htr267a, htr367a])
                    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                      linarith only [hlam, hc236xy, htr016b, htr067a, htr123a, htr126b, htr267a])
                    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                    have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                      linarith only [hlam, hc569xy, htr056c, htr059a, htr067a, htr567a])
                    obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                    have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr159a, htr159b, htr159c, _, _⟩
                      linarith only [hlam, hc235xy, htr025c, htr059a, htr123a, htr125b, htr159a])
                    obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
                    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
                      linarith only [hlam, hd01b, hd56a, htr015a, htr159a, htr456a, htr459a])
                    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
                    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                      linarith only [hlam, hd01b, hd910a, htr014a, htr145a, htr459a, htr5910a])
                    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc356zy, htr237c, htr278a, htr367c, htr567a, htr678a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hc356zy, htr367a, htr567b, htr579a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd23a, hd89b, htr123a, htr127a, htr278a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hd23a, hd78b, htr123a, htr128a, htr289a, htr789a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc238xy, htr123a, htr128b, htr189a, htr289a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd01b, hd56a, htr018a, htr189a, htr568a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, hc056zy, htr068a, htr568b, htr589a, htr689a])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                      linarith only [hlam, hc568yz, htr068a, htr069a, htr589a, htr689b])
                    obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hd56a, hd910b, htr067a, htr069a, htr567a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc578yz, htr589a, htr679c, htr6910a, htr789c, htr8910a]
                    ·
                      linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]

theorem shard_559 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127b : m.d 1 2 < m.d 1 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_559 m htr014a htr014b htr015a htr015b htr016a htr016b htr017a htr017b htr018a htr018b htr024c htr025c htr026c htr027c htr035c htr123a htr124a htr124b htr125a htr125b htr126a htr126b htr127a htr127b htr128a htr128b htr129a htr235c htr236c htr237c htr238c htr239c htr345a

#print axioms shard_559
end Jsp404.NoSatElevenDBMTerminal
