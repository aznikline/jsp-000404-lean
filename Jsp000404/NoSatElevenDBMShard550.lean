import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_550 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr029c : m.d 0 9 < m.d 0 2)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr056a : m.d 0 5 + lam ≤ m.d 5 6)
    (htr056c : m.d 0 6 < m.d 5 6)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd04a := (m.hrange 0 4 (by decide)).1
  have hd28a := (m.hrange 2 8 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
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
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc239xy, hc239yx, hc239yz, hc239zy⟩ := endpoint_caps m 2 3 9 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc258xy, hc258yx, hc258yz, hc258zy⟩ := endpoint_caps m 2 5 8 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, hc458yx, htr045b, htr048a, htr056a, htr456a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
    linarith only [hlam, hc459yx, htr045b, htr049a, htr056a, htr456a])
  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr056a, htr057a, htr567b])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr056c, htr067a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, htr015b, htr056a, htr125b, htr257a, htr567b])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc235yx, htr123a, htr126a, htr256a, htr267a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr235b, htr256a, htr357a, htr567b])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc578yx, htr056a, htr058a, htr456a, htr457a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
        linarith only [hlam, hc579yx, htr056a, htr059a, htr456a, htr457a])
      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc678yx, htr456a, htr457a, htr567c, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc679yx, htr456a, htr457a, htr567c, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd35a, hd78b, htr356a, htr456a, htr457a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd35a, hd79b, htr356a, htr456a, htr457a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      rcases m.htr 4 5 8 (by decide) (by decide) with
        ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
      ·
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc235yx, hc578zy, htr123a, htr127a, htr256a, htr278a, htr456a, htr458a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd35a, hd89b, htr356a, htr456a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd35a, hd810b, htr356a, htr456a, htr458a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc257yz, htr278a, htr578c, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc257yz, htr278b, htr289a, htr578a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc235yx, hc589zy, htr123a, htr128a, htr256a, htr289a, htr456a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc257yz, htr278a, htr578c, htr5810a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc257yz, htr278b, htr2810a, htr578a, htr7810a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc235yx, hc8910yz, htr123a, htr128a, htr256a, htr2810a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc015yx, hc689zy, htr012a, htr059a, htr128a, htr289a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd57b, hd89a, htr457a, htr459a, htr5910a, htr8910a]
        ·
          linarith only [hlam, hd01b, hd910a, htr012a, htr128a, htr289a, htr8910a]
      ·
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc257yz, htr278a, htr457a, htr458a, htr578b])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd57b, hd78a, htr457a, htr458a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc015yx, hc678zy, htr012a, htr058a, htr127a, htr278a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc235yx, hc789yz, htr123a, htr127a, htr256a, htr279a, htr568a, htr689a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc235yx, hc8910yx, htr123a, htr128a, htr256a, htr2810a, htr568a, htr689a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc257yz, htr279a, htr457a, htr459a, htr579b])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd28a, hd57b, htr2810a, htr457a, htr458a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd35a, hd910b, htr356a, htr456a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc015yx, hc678zy, htr012a, htr058a, htr127a, htr278a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, hc235yx, hc8910zy, htr123a, htr129a, htr256a, htr2910a, htr568a, htr6810a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc257yz, htr279a, htr579c, htr5910a, htr7910a]
        ·
          linarith only [hlam, hc257yz, htr279b, htr2910a, htr579a, htr7910a]
    ·
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr056c, htr068a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr015b, htr056a, htr125b, htr258a, htr568b])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, htr457c, htr458b, htr478c])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, htr457b, htr478a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc789yx, htr457a, htr458a, htr578c, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hc7810yx, htr457a, htr458a, htr5710a, htr578c])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd35a, hd89b, htr356a, htr456a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd35a, hd67b, htr356a, htr456a, htr458a, htr578c, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hd35a, hd78b, htr356a, htr567b, htr579a, htr678a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
            linarith only [hlam, hc235yx, hc789zy, htr123a, htr128a, htr256a, htr289a, htr567a, htr679a])
          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, hc258yz, htr289a, htr458a, htr459a, htr589b])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd35a, hd910b, htr356a, htr456a, htr459a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hd35a, hd78b, htr356a, htr567b, htr5710a, htr6710a, htr678a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
            linarith only [hlam, hc235yx, hc7910zy, htr123a, htr129a, htr256a, htr2910a, htr567a, htr6710a])
          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc258yz, htr289a, htr589c, htr5910a, htr8910a]
          ·
            linarith only [hlam, hc258yz, htr289b, htr2910a, htr589a, htr8910a]
        ·
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            rcases m.htr 4 5 9 (by decide) (by decide) with
              ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
            ·
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, htr457c, htr459b, htr479c])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, htr458c, htr459b, htr489c])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, htr457b, htr479a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc789xy, htr457a, htr459a, htr578a, htr579c])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, htr458b, htr489a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd35a, hd67b, htr356a, htr456a, htr459a, htr579c, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd35a, hd79b, htr356a, htr567b, htr578a, htr678a, htr679a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd35a, hd89b, htr356a, htr567a, htr678a, htr789a]
              ·
                linarith only [hlam, hd35a, hd78b, htr356a, htr456a, htr459a, htr589c, htr789a]
            ·
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                rcases m.htr 4 5 10 (by decide) (by decide) with
                  ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                ·
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, htr4510b, htr457c, htr4710c])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, htr4510b, htr458c, htr4810c])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, htr457b, htr4710a, htr5710a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc7810xy, htr4510a, htr457a, htr5710c, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                    linarith only [hlam, htr458b, htr4810a, htr5810a])
                  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd35a, hd67b, htr356a, htr4510a, htr456a, htr5710c, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd35a, hd710b, htr356a, htr567b, htr578a, htr6710a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  rcases m.htr 7 8 10 (by decide) (by decide) with
                    ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  ·
                    linarith only [hlam, hd35a, hd810b, htr356a, htr567a, htr678a, htr7810a]
                  ·
                    linarith only [hlam, hd35a, hd78b, htr356a, htr4510a, htr456a, htr5810c, htr7810a]
                ·
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, hc235yx, hc789yx, htr123a, htr127a, htr256a, htr279a, htr567a, htr678a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                      linarith only [hlam, hc235yx, hc7810yx, htr123a, htr127a, htr256a, htr2710a, htr567a, htr678a])
                    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                      linarith only [hlam, hc245yz, htr257b, htr279a, htr457a, htr579a])
                    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                      linarith only [hlam, hc245yz, htr257b, htr2710a, htr457a, htr5710a])
                    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hd35a, hd78b, htr356a, htr567b, htr579a, htr678a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hc235yx, hc789zy, htr123a, htr128a, htr256a, htr289a, htr567a, htr679a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hc245yz, htr258b, htr289a, htr458a, htr589a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                      linarith only [hlam, hd35a, hd78b, htr356a, htr567b, htr5710a, htr6710a, htr678a])
                    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                    have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                      linarith only [hlam, hc235yx, hc7910zy, htr123a, htr129a, htr256a, htr2910a, htr567a, htr6710a])
                    obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd35a, hd89b, htr356a, htr567a, htr678a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hd35a, hd910b, htr356a, htr567a, htr679a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd35a, hd79b, htr356a, htr568b, htr589a, htr7910a, htr8910a]
                    ·
                      linarith only [hlam, hc278yz, htr289b, htr2910a, htr789a, htr8910a]
                  ·
                    rcases m.htr 3 7 8 (by decide) (by decide) with
                      ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
                    ·
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, hc345yz, htr057c, htr078a, htr357b, htr378a, htr457a])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr457c, htr478a, htr567b, htr578a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                        linarith only [hlam, hd35a, hd79b, htr356a, htr567b, htr578a, htr678a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      rcases m.htr 5 7 9 (by decide) (by decide) with
                        ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                      ·
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, htr057c, htr079a, htr579a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc235yx, htr123a, htr127a, htr256a, htr279a, htr567b, htr579a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hc567yz, htr478a, htr479a, htr579a, htr678a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        rcases m.htr 5 7 10 (by decide) (by decide) with
                          ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                        ·
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                              linarith only [hlam, hc235yx, hc8910yx, htr123a, htr128a, htr256a, htr2810a, htr567b, htr578a, htr789a])
                            obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                            have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                              linarith only [hlam, hc367yz, htr238b, htr2810a, htr378b, htr478c, htr4810a, htr678a])
                            obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                              linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a])
                            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                            have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                              linarith only [hlam, hd04a, hd89b, htr048a, htr4810a, htr6810a, htr689a])
                            obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                            have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                              linarith only [hlam, hc235yx, hc8910zy, htr123a, htr129a, htr256a, htr2910a, htr568a, htr6810a])
                            obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                              linarith only [hlam, hc267yz, htr279b, htr2910a, htr679a, htr7910a])
                            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                            rcases m.htr 8 9 10 (by decide) (by decide) with
                              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                            ·
                              linarith only [hlam, hd35a, hd910b, htr356a, htr567b, htr578a, htr789a, htr8910a]
                            ·
                              linarith only [hlam, hd35a, hd89b, htr356a, htr567b, htr579a, htr7910a, htr8910a]
                          ·
                            have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                              linarith only [hlam, hc367yz, htr238b, htr289a, htr378b, htr678a, htr789a])
                            obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                              linarith only [hlam, hc235yx, hc8910xy, htr123a, htr128a, htr256a, htr289a, htr567b, htr578a, htr7810a])
                            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                            have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                              linarith only [hlam, hc367yz, htr238b, htr2810a, htr378b, htr678a, htr7810a])
                            obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                              linarith only [hlam, hc235yx, hc8910yz, htr123a, htr128a, htr256a, htr2810a, htr569a, htr6910a])
                            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                              linarith only [hlam, hc014yx, hc689zy, htr012a, htr049a, htr128a, htr289a, htr4910a, htr6910a])
                            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                            have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                              linarith only [hlam, hc267yz, htr279b, htr2910a, htr479c, htr4910a, htr679a])
                            obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                            rcases m.htr 8 9 10 (by decide) (by decide) with
                              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                            ·
                              linarith only [hlam, hd01b, hd89a, htr012a, htr129a, htr2910a, htr8910a]
                            ·
                              linarith only [hlam, hd01b, hd910a, htr012a, htr128a, htr289a, htr8910a]
                        ·
                          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                            linarith only [hlam, hc067yz, htr0710a, htr5710a, htr578a, htr678a])
                          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                            linarith only [hlam, htr0710c, htr078b, htr0810b])
                          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                          have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                            linarith only [hlam, htr0710c, htr079b, htr0910b])
                          obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                          have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                            linarith only [hlam, hc238yx, htr023a, htr028c, htr0810a, htr2810a])
                          obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                            linarith only [hlam, hc239yx, htr023a, htr029c, htr0910a, htr2910a])
                          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hc235yx, hc8910yx, htr123a, htr128a, htr256a, htr2810a, htr567b, htr578a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                            linarith only [hlam, hc367yz, htr238b, htr289a, htr378b, htr678a, htr789a])
                          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd01b, hd89a, htr012a, htr129a, htr2910a, htr8910a]
                          ·
                            linarith only [hlam, hd01b, hd910a, htr012a, htr128a, htr289a, htr8910a]
                      ·
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, hc067yz, htr079a, htr578a, htr579a, htr678a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, htr078b, htr079c, htr089b])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc267yz, htr279a, htr578a, htr579a, htr678a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                          linarith only [hlam, hc238yx, htr023a, htr028c, htr089a, htr289a])
                        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, htr457b, htr479a, htr579a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc235yx, hc8910xy, htr123a, htr128a, htr256a, htr289a, htr567b, htr578a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                          linarith only [hlam, hc367yz, htr238b, htr2810a, htr378b, htr678a, htr7810a])
                        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hc235yx, hc8910yz, htr123a, htr128a, htr256a, htr2810a, htr569a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                          linarith only [hlam, hc014yx, hc679zy, htr012a, htr049a, htr127a, htr279a, htr4910a, htr6910a])
                        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd67b, hd89a, htr478a, htr479c, htr4910a, htr678a, htr8910a]
                        ·
                          linarith only [hlam, hd01b, hd910a, htr012a, htr128a, htr289a, htr8910a]
                    ·
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc014yx, htr013a, htr047a, htr137a, htr378a, htr478a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                        linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a])
                      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc245yz, htr258b, htr289a, htr458a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hc235yx, hc678zy, htr123a, htr127a, htr237b, htr256a, htr378a, htr568b, htr589a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, hc235yx, hc789yz, htr123a, htr127a, htr256a, htr279a, htr568a, htr689a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                        linarith only [hlam, hc235yx, hc8910yx, htr123a, htr128a, htr256a, htr2810a, htr568a, htr689a])
                      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc245yz, htr257b, htr279a, htr457a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hc345yz, htr356a, htr457c, htr479a, htr567b, htr579a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                        linarith only [hlam, hc238yx, hc789xy, htr123a, htr127a, htr237b, htr2810a, htr378a, htr478c, htr479a, htr4810a])
                      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                        linarith only [hlam, hc014yx, hc678zy, htr013a, htr048a, htr137a, htr378a, htr4810a, htr6810a])
                      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                      have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                        linarith only [hlam, hc235yx, hc8910zy, htr123a, htr129a, htr256a, htr2910a, htr568a, htr6810a])
                      obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                        linarith only [hlam, hc789xy, htr237b, htr279b, htr2910a, htr378a, htr7910a])
                      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd35a, hd910b, htr356a, htr568a, htr689a, htr8910a]
                      ·
                        linarith only [hlam, hd78a, hd89b, htr237b, htr279a, htr378a, htr7910a, htr8910a]
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, hc345yz, htr036b, htr0610a, htr356b, htr456a, htr5610a])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                  linarith only [hlam, htr0610c, htr067b, htr0710b])
                obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0610c, htr068b, htr0810b])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                  linarith only [hlam, hc345yz, htr236b, htr2610a, htr356b, htr456a, htr5610a])
                obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
                have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                  linarith only [hlam, hc237yx, htr023a, htr027c, htr0710a, htr2710a])
                obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hc238yx, htr023a, htr028c, htr0810a, htr2810a])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc235yx, hc7810yx, htr123a, htr127a, htr256a, htr2710a, htr567a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc6710yx, htr2610a, htr267b, htr278a, htr678a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                rcases m.htr 7 8 10 (by decide) (by decide) with
                  ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                ·
                  linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr2810a, htr7810a]
                ·
                  linarith only [hlam, hd01b, hd810a, htr012a, htr127a, htr278a, htr7810a]
          ·
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, hc345yz, htr036b, htr069a, htr356b, htr456a, htr569a])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, htr067b, htr069c, htr079b])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
              linarith only [hlam, htr068b, htr069c, htr089b])
            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
            have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr269a, htr269b, htr269c, _, _⟩
              linarith only [hlam, hc345yz, htr236b, htr269a, htr356b, htr456a, htr569a])
            obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, hc237yx, htr023a, htr027c, htr079a, htr279a])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr289a, htr289b, htr289c, _, _⟩
              linarith only [hlam, hc238yx, htr023a, htr028c, htr089a, htr289a])
            obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hc235yx, hc789yx, htr123a, htr127a, htr256a, htr279a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc679yx, htr267b, htr269a, htr278a, htr678a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
            ·
              linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc678yx, htr056a, htr058a, htr567a, htr568b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc345yz, htr036b, htr068a, htr356b, htr456a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr067b, htr068c, htr078b])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc345yz, htr236b, htr268a, htr356b, htr456a, htr568a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc237yx, htr023a, htr027c, htr078a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr456b, htr468a, htr568a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc235yx, hc789xy, htr123a, htr127a, htr256a, htr278a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, hc678yx, htr067b, htr068a, htr079a, htr679a])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc678yx, htr267b, htr268a, htr279a, htr679a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc579zy, htr057c, htr079a, htr457a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          linarith only [hlam, hc235yx, hc7810xy, htr123a, htr127a, htr256a, htr278a, htr567a, htr6710a])
        obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
        have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
          linarith only [hlam, hc678yx, htr267b, htr268a, htr2710a, htr6710a])
        obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr012a, htr126a, htr268a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, hc678yx, htr058c, htr089a, htr567a, htr568c, htr689a])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, htr058b, htr059c, htr089b])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr259a, htr259b, htr259c, _, _⟩
          linarith only [hlam, htr015b, htr059a, htr125b, htr259a])
        obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc678yx, htr467a, htr468c, htr489a, htr689a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd01b, hd910a, htr012a, htr127a, htr279a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, hd01b, hd79a, htr012a, htr129a, htr2910a, htr7910a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc245yz, htr259b, htr2910a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc014yx, hc7910yz, htr012a, htr048a, htr127a, htr2710a, htr489a, htr8910a]
        ·
          linarith only [hlam, hc015yx, hc789yz, htr012a, htr059a, htr127a, htr279a, htr5910a, htr8910a]
  ·
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc345yz, htr036b, htr067a, htr356b, htr456a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc345yz, htr236b, htr267a, htr356b, htr456a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc237yx, htr023a, htr027c, htr078a, htr278a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd01b, hd79a, htr012a, htr126a, htr267a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr279a, htr679a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    rcases m.htr 3 5 7 (by decide) (by decide) with
      ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc345yz, htr056a, htr057a, htr357a, htr456a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr057b, htr058c, htr078b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc345yz, htr237b, htr278a, htr357b, htr456a, htr567c, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc345yz, htr237b, htr279a, htr357b, htr456a, htr567c, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      rcases m.htr 4 5 8 (by decide) (by decide) with
        ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
      ·
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          linarith only [hlam, hc678xy, htr456a, htr458a, htr567a, htr568c]
        ·
          linarith only [hlam, hc568zy, htr456a, htr458a, htr568a]
      ·
        rcases m.htr 4 5 9 (by decide) (by decide) with
          ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
        ·
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            linarith only [hlam, hc679xy, htr456a, htr459a, htr567a, htr569c]
          ·
            linarith only [hlam, hc569zy, htr456a, htr459a, htr569a]
        ·
          rcases m.htr 3 6 8 (by decide) (by decide) with
            ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc345yz, htr056c, htr068a, htr356b, htr368a, htr456a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            rcases m.htr 5 6 9 (by decide) (by decide) with
              ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, htr056c, htr069a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hc235yx, htr123a, htr126a, htr256a, htr269a, htr569a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                rcases m.htr 3 8 9 (by decide) (by decide) with
                  ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
                ·
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc678xy, htr367a, htr368b, htr389a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                    linarith only [hlam, hc235yx, hc8910yx, htr123a, htr128a, htr256a, htr2810a, htr568a, htr689a])
                  obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc678xy, htr238b, htr2810a, htr367a, htr368b, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                    linarith only [hlam, hc235yx, hc8910zy, htr123a, htr129a, htr256a, htr2910a, htr568a, htr6810a])
                  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc679xy, htr267a, htr269b, htr2910a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd67a, hd910b, htr367a, htr368a, htr689a, htr8910a]
                  ·
                    linarith only [hlam, hd35a, hd89b, htr356a, htr569a, htr6910a, htr8910a]
                ·
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc235yx, hc8910xy, htr123a, htr128a, htr238b, htr256a, htr389a, htr568a, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                    linarith only [hlam, hc678xy, htr238b, htr2810a, htr367a, htr368b, htr6810a])
                  obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc235yx, hc8910yz, htr123a, htr128a, htr256a, htr2810a, htr569a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                    linarith only [hlam, hc679xy, htr267a, htr269b, htr2910a, htr6910a])
                  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd01b, hd89a, htr012a, htr129a, htr2910a, htr8910a]
                  ·
                    linarith only [hlam, hd01b, hd910a, htr013a, htr138a, htr389a, htr8910a]
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, hc678xy, htr0610a, htr067a, htr5610a, htr568a])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0610c, htr068b, htr0810b])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                  linarith only [hlam, htr0610c, htr069b, htr0910b])
                obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hc238yx, htr023a, htr028c, htr0810a, htr2810a])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                  linarith only [hlam, hc239yx, htr023a, htr029c, htr0910a, htr2910a])
                obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc235yx, hc8910yx, htr123a, htr128a, htr256a, htr2810a, htr568a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hc678xy, htr238b, htr289a, htr367a, htr368b, htr689a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd01b, hd89a, htr012a, htr129a, htr2910a, htr8910a]
                ·
                  linarith only [hlam, hd01b, hd910a, htr012a, htr128a, htr289a, htr8910a]
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc678xy, htr067a, htr069a, htr568a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, htr068b, htr069c, htr089b])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hc678xy, htr267a, htr269a, htr568a, htr569a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc238yx, htr023a, htr028c, htr089a, htr289a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, htr456b, htr469a, htr569a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc235yx, hc8910xy, htr123a, htr128a, htr256a, htr289a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                linarith only [hlam, hc678xy, htr238b, htr2810a, htr367a, htr368b, htr6810a])
              obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd01b, hd910a, htr012a, htr126a, htr269a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc689yx, htr468a, htr469c, htr4910a, htr6910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc015yx, hc8910yz, htr012a, htr057a, htr128a, htr2810a, htr579a, htr7910a]
              ·
                linarith only [hlam, hc014yx, hc679yz, htr012a, htr049a, htr126a, htr269a, htr4910a, htr7910a]
          ·
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hd01b, hd89a, htr013a, htr136a, htr368a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr289a, htr289b, htr289c, _, _⟩
              linarith only [hlam, hd01b, hd68a, htr012a, htr128a, htr289a, htr689a])
            obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc345yz, htr237b, htr278b, htr289a, htr357b, htr458a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
              linarith only [hlam, hd01b, hd810a, htr013a, htr136a, htr368a, htr6810a])
            obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
            have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
              linarith only [hlam, hd01b, hd68a, htr012a, htr128a, htr2810a, htr6810a])
            obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
            have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
              linarith only [hlam, hc345yz, htr237b, htr278b, htr2810a, htr357b, htr458a, htr5810a])
            obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc015yx, hc678yz, htr013a, htr058a, htr136a, htr368a, htr589a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr269a, htr269b, htr269c, _, _⟩
              linarith only [hlam, hc015yx, hc689yz, htr012a, htr057a, htr126a, htr269a, htr578a, htr789a])
            obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc015yx, hc678yz, htr013a, htr058a, htr136a, htr368a, htr5810a, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
              linarith only [hlam, hc015yx, hc8910zy, htr012a, htr057a, htr129a, htr2910a, htr578a, htr7810a])
            obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc679xy, htr267a, htr269b, htr2910a, htr6910a])
            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hd35a, hd910b, htr357a, htr578a, htr789a, htr8910a]
            ·
              linarith only [hlam, hd67a, hd89b, htr267a, htr269a, htr6910a, htr8910a]
    ·
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
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr012a, htr126a, htr268a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hd01b, hd68a, htr012a, htr128a, htr289a, htr689a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd01b, hd910a, htr012a, htr126a, htr269a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc014yx, hc689yz, htr012a, htr047a, htr126a, htr269a, htr478a, htr789a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc237yx, hc679yz, htr123a, htr126a, htr269a, htr278a, htr478a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc467zy, htr479a, htr679b, htr6910a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc237yx, hc6910yz, htr123a, htr126a, htr2610a, htr278a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc237yx, hc689yz, htr123a, htr126a, htr269a, htr279a, htr7910a, htr8910a]
      ·
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc237yx, hc678yz, htr123a, htr126a, htr268a, htr279a, htr478a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc014yx, hc6910yz, htr012a, htr047a, htr126a, htr2610a, htr479a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc238yx, hc679yz, htr123a, htr126a, htr269a, htr289a, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]

theorem shard_550 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr029c : m.d 0 9 < m.d 0 2)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr056a : m.d 0 5 + lam ≤ m.d 5 6)
    (htr056c : m.d 0 6 < m.d 5 6)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False :=
  proof_shard_550 m htr012a htr013a htr015b htr023a htr027c htr028c htr029c htr036b htr045b htr056a htr056c htr123a htr125b htr126a htr127a htr128a htr129a htr136a htr137a htr138a htr235b htr236b htr237b htr238b htr256a htr356a htr356b htr456a htr456b htr456c

#print axioms shard_550
end Jsp404.NoSatElevenDBMTerminal
