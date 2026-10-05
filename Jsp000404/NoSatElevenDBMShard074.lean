import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_074 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr028b : m.d 0 2 < m.d 0 8)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr056c : m.d 0 6 < m.d 0 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd05a, hd05braw⟩ := m.hrange 0 5 (by decide)
  have hd05b : m.d 0 5 < 4*lam := by
    linarith only [hd05braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < 4*lam := by
    linarith only [hd26braw, hp]
  obtain ⟨hd28a, hd28braw⟩ := m.hrange 2 8 (by decide)
  have hd28b : m.d 2 8 < 4*lam := by
    linarith only [hd28braw, hp]
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
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
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  rcases m.htr 4 5 7 (by decide) (by decide) with
    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc567xy, htr045a, htr047a, htr456a, htr457c])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, htr456c, htr457b, htr467c])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, htr456b, htr467a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc256zy, htr267a, htr456a, htr457a, htr567c])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc678yx, htr456a, htr457a, htr567c, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hc679yx, htr456a, htr457a, htr567c, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr278a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc237xy, htr023a, htr027b, htr078a, htr278a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, htr047c, htr048b, htr078c])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd56a, hd67b, htr456a, htr457a, htr578a, htr678a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd01a, hd79b, htr012a, htr126a, htr267a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd56a, hd67b, htr456a, htr457a, htr579a, htr679a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hc567xy, htr456a, htr457b, htr479a, htr579a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc256zy, htr268a, htr456a, htr458a, htr568c])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr012a, htr126a, htr268a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd56a, hd68b, htr456a, htr458a, htr589a, htr689a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc568xy, htr456a, htr458b, htr489a, htr589a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hd01a, hd810b, htr012a, htr126a, htr268a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
        linarith only [hlam, hd56a, hd68b, htr456a, htr458a, htr5810a, htr6810a])
      obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hc568xy, htr456a, htr458b, htr4810a, htr5810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc014xy, hc678zy, htr012a, htr048a, htr126a, htr268a, htr489a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hc014xy, hc689zy, htr012a, htr047a, htr126a, htr269a, htr478a, htr789a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc236xy, htr023a, htr026b, htr069a, htr269a])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc567xy, htr056c, htr057a, htr069a, htr569a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr459a, htr459b, htr459c, _, _⟩
        linarith only [hlam, hc256zy, htr269a, htr456a, htr459a, htr569c])
      obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
      have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
        linarith only [hlam, hd05b, hd910a, htr057a, htr458a, htr459a, htr578c, htr5910a])
      obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd59a, hd67b, htr267a, htr269a, htr5910a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
        linarith only [hlam, hc679yx, htr267a, htr269c, htr2910a, htr6910a])
      obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
      rcases m.htr 7 8 10 (by decide) (by decide) with
        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
      ·
        linarith only [hlam, hc014xy, hc678zy, htr012a, htr048a, htr126a, htr268a, htr4810a, htr7810a]
      ·
        linarith only [hlam, hc014xy, hc8910yz, htr012a, htr047a, htr129a, htr2910a, htr478a, htr7810a]
    ·
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc234xy, htr123a, htr125a, htr245a, htr258a, htr458a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      rcases m.htr 3 5 7 (by decide) (by decide) with
        ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
      ·
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc567xy, htr236c, htr268a, htr356c, htr357a, htr568a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, hc567xy, htr236c, htr269a, htr356c, htr357a, htr569a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc234xy, hc689zy, htr123a, htr126a, htr245a, htr269a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc578yx, htr235c, htr258c, htr289a, htr357a, htr589a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hd01a, hd89b, htr012a, htr126a, htr268a, htr689a]
        ·
          linarith only [hlam, hd01a, hd68b, htr012a, htr128a, htr289a, htr689a]
      ·
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hd01a, hd35b, htr012a, htr125a, htr257a, htr357a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, hc235xy, hc568yz, htr123a, htr126a, htr257a, htr268a, htr457a, htr458a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc236xy, htr023a, htr026b, htr068a, htr268a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd35b, hd89a, htr357a, htr457a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd35b, hd810a, htr357a, htr457a, htr458a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd58a, hd67b, htr267a, htr268a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc678yx, htr267a, htr268c, htr289a, htr689a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc235xy, hc589yz, htr123a, htr128a, htr257a, htr289a, htr457a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, hc056zy, htr069a, htr456a, htr459a, htr569c])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hd58a, hd67b, htr267a, htr268a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc678yx, htr267a, htr268c, htr2810a, htr6810a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd56a, hd910b, htr068a, htr069a, htr568a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd56a, hd69b, htr456a, htr459a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc235xy, hc789yz, htr123a, htr128a, htr257a, htr289a, htr579c, htr5910a, htr7910a]
        ·
          linarith only [hlam, hc014xy, hc8910zy, htr012a, htr047a, htr128a, htr2810a, htr479a, htr7910a]
  ·
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr456c, htr458b, htr468c])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, htr457c, htr458b, htr478c])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, htr456b, htr468a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc256zy, htr268a, htr456a, htr458a, htr568c])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc678xy, htr456a, htr458a, htr567a, htr568c])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc689yx, htr456a, htr458a, htr568c, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, htr457b, htr478a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc257zy, htr278a, htr457a, htr458a, htr578c])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc789yx, htr457a, htr458a, htr578c, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hc7810yx, htr457a, htr458a, htr5710a, htr578c])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc567yz, htr457a, htr458a, htr578c, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc236xy, htr023a, htr026b, htr067a, htr267a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc568xy, htr056c, htr058a, htr067a, htr567a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
        linarith only [hlam, hc569xy, htr058a, htr059a, htr456a, htr458a])
      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd57a, hd68b, htr267a, htr268a, htr579a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hd56a, hd78b, htr278a, htr279a, htr567a, htr679a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr459a, htr459b, htr459c, _, _⟩
        linarith only [hlam, hc015xy, hc579yz, htr012a, htr058a, htr127a, htr279a, htr458a, htr459a])
      obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc056zy, htr069a, htr456a, htr459a, htr569c])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        linarith only [hlam, hd57a, hd68b, htr267a, htr268a, htr5710a, htr6710a])
      obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hd56a, hd78b, htr2710a, htr278a, htr567a, htr6710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr012a, htr126a, htr268a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd56a, hd68b, htr456a, htr458a, htr589a, htr689a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd56a, hd910b, htr067a, htr069a, htr567a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
        linarith only [hlam, hd56a, hd69b, htr456a, htr459a, htr5910a, htr6910a])
      obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc015xy, hc789zy, htr012a, htr059a, htr127a, htr279a, htr5910a, htr8910a]
      ·
        linarith only [hlam, hc015xy, hc7910zy, htr012a, htr058a, htr127a, htr2710a, htr589a, htr8910a]
    ·
      rcases m.htr 4 5 9 (by decide) (by decide) with
        ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
      ·
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, htr456c, htr459b, htr469c])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, htr457c, htr459b, htr479c])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, htr456b, htr469a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, hc256zy, htr269a, htr456a, htr459a, htr569c])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hc679xy, htr456a, htr459a, htr567a, htr569c])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, htr457b, htr479a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc257zy, htr279a, htr457a, htr459a, htr579c])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc789xy, htr457a, htr459a, htr578a, htr579c])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc567yz, htr457a, htr459a, htr579c, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hd01a, hd79b, htr012a, htr126a, htr267a, htr679a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc236xy, htr023a, htr026b, htr067a, htr267a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc569xy, htr056c, htr059a, htr067a, htr567a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc015xy, hc578yz, htr012a, htr059a, htr127a, htr278a, htr458a, htr459a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hd56a, hd79b, htr278a, htr279a, htr567a, htr678a]
        ·
          linarith only [hlam, hd57a, hd69b, htr267a, htr269a, htr578a, htr678a]
      ·
        rcases m.htr 4 5 10 (by decide) (by decide) with
          ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
        ·
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, htr4510b, htr456c, htr4610c])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, htr4510b, htr457c, htr4710c])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, htr456b, htr4610a, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
            linarith only [hlam, hc256zy, htr2610a, htr4510a, htr456a, htr5610c])
          obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc6710xy, htr4510a, htr456a, htr5610c, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, htr457b, htr4710a, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
            linarith only [hlam, hc257zy, htr2710a, htr4510a, htr457a, htr5710c])
          obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc7810xy, htr4510a, htr457a, htr5710c, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc567yz, htr4510a, htr457a, htr5710c, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hd01a, hd710b, htr012a, htr126a, htr267a, htr6710a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc236xy, htr023a, htr026b, htr067a, htr267a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
            linarith only [hlam, hc5610xy, htr0510a, htr056c, htr067a, htr567a])
          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc015xy, hc578yz, htr012a, htr0510a, htr127a, htr278a, htr4510a, htr458a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd56a, hd710b, htr2710a, htr278a, htr567a, htr678a]
          ·
            linarith only [hlam, hd57a, hd610b, htr2610a, htr267a, htr578a, htr678a]
        ·
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            rcases m.htr 3 6 7 (by decide) (by decide) with
              ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
            ·
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc234xy, hc678yx, htr123a, htr126a, htr236c, htr245a, htr367a, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd01a, hd78b, htr013a, htr136a, htr367a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd01a, hd79b, htr013a, htr136a, htr367a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr279a, htr679a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hc567yz, htr236c, htr268a, htr367a, htr578a, htr678b])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd01a, hd89b, htr012a, htr126a, htr268a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hd01a, hd810b, htr012a, htr126a, htr268a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                  linarith only [hlam, hc234xy, hc689zy, htr123a, htr126a, htr245a, htr269a, htr458a, htr589a])
                obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  linarith only [hlam, hc567yz, htr578a, htr678c, htr6810a, htr7810a])
                obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                  linarith only [hlam, hc567yz, htr578b, htr5810a, htr678a, htr7810a])
                obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                  linarith only [hlam, hc234xy, hc8910yz, htr123a, htr129a, htr245a, htr2910a, htr458a, htr5810a])
                obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hc679yx, htr236c, htr269c, htr2910a, htr367a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd67b, hd89a, htr236c, htr269a, htr367a, htr6910a, htr8910a]
                ·
                  linarith only [hlam, hd34b, hd910a, htr345a, htr458a, htr589a, htr8910a]
              ·
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hc234xy, hc678zy, htr123a, htr126a, htr245a, htr268a, htr457a, htr578a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc236xy, htr023a, htr026b, htr068a, htr268a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd34b, hd89a, htr345a, htr457a, htr578a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd67b, hd78a, htr236c, htr268a, htr367a, htr689a, htr789a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hc678yx, htr236c, htr268c, htr289a, htr367a, htr689a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc234xy, hc789yz, htr123a, htr128a, htr245a, htr289a, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hc567yz, htr036c, htr069a, htr367a, htr579a, htr679b])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc8910yx, htr068a, htr069a, htr6810a, htr689c])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hc678yx, htr236c, htr268c, htr2810a, htr367a, htr6810a])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                  linarith only [hlam, hc234xy, hc8910zy, htr123a, htr128a, htr245a, htr2810a, htr459a, htr5910a])
                obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd56a, hd910b, htr068a, htr069a, htr568a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
                ·
                  linarith only [hlam, hc237xy, hc589yz, htr123a, htr128a, htr279a, htr289a, htr5910a, htr7910a]
            ·
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hd01a, hd36b, htr012a, htr126a, htr267a, htr367a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hc236xy, htr023a, htr026b, htr067a, htr267a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              rcases m.htr 4 6 7 (by decide) (by decide) with
                ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
              ·
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc356zy, htr237c, htr278a, htr367c, htr567a, htr678a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc234xy, hc789yx, htr123a, htr127a, htr245a, htr278a, htr457a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, hc234xy, hc7810yx, htr123a, htr127a, htr245a, htr278a, htr457a, htr5710a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc356zy, htr367a, htr567b, htr579a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc356zy, htr237c, htr279a, htr367c, htr567a, htr679a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc234xy, hc789zy, htr123a, htr127a, htr245a, htr279a, htr458a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hc356zy, htr367a, htr567b, htr5710a, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                    linarith only [hlam, hc356zy, htr237c, htr2710a, htr367c, htr567a, htr6710a])
                  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                    linarith only [hlam, hc234xy, hc7910zy, htr123a, htr127a, htr245a, htr2710a, htr459a, htr5910a])
                  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd01a, hd89b, htr012a, htr127a, htr278a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd01a, hd910b, htr012a, htr127a, htr279a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]
                ·
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc234xy, hc789xy, htr123a, htr127a, htr245a, htr279a, htr457a, htr578a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                    linarith only [hlam, hc234xy, hc7810xy, htr123a, htr127a, htr245a, htr2710a, htr457a, htr578a])
                  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc356zy, htr237c, htr279a, htr367c, htr567a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc356zy, htr367a, htr567b, htr579a, htr679a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc234xy, hc789yz, htr123a, htr128a, htr245a, htr289a, htr457a, htr579a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hc356zy, htr237c, htr2710a, htr367c, htr567a, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, hc356zy, htr367a, htr567b, htr5710a, htr6710a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                    linarith only [hlam, hc234xy, hc7910yz, htr123a, htr129a, htr245a, htr2910a, htr457a, htr5710a])
                  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd34b, hd89a, htr345a, htr457a, htr578a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd34b, hd910a, htr345a, htr457a, htr579a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc278zy, htr289c, htr2910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hc278zy, htr289a, htr789b, htr7910a, htr8910a]
              ·
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd34b, hd68a, htr346a, htr467a, htr567a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                rcases m.htr 4 6 8 (by decide) (by decide) with
                  ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc056zy, htr068a, htr467a, htr468a, htr567a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, htr067c, htr068b, htr078c])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, hc256zy, htr268a, htr467a, htr468a, htr567a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc237xy, htr023a, htr027b, htr078a, htr278a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc234xy, hc789yx, htr123a, htr127a, htr246a, htr278a, htr467a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc356zy, htr237c, htr279a, htr367c, htr567a, htr679a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc234xy, hc789zy, htr123a, htr127a, htr245a, htr279a, htr458a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc234xy, hc568yz, htr123a, htr126a, htr245a, htr268a, htr458c, htr489a, htr589a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd01a, hd89b, htr012a, htr127a, htr278a, htr789a]
                  ·
                    linarith only [hlam, hd56a, hd78b, htr467a, htr468b, htr489a, htr567a, htr789a]
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, htr046b, htr068a, htr468a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, hc234xy, htr123a, htr126a, htr246a, htr268a, htr468a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  rcases m.htr 4 6 9 (by decide) (by decide) with
                    ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                  ·
                    have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                      linarith only [hlam, hc056zy, htr069a, htr467a, htr469a, htr567a])
                    obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, htr067c, htr069b, htr079c])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr068c, htr069b, htr089c])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, hc237xy, htr023a, htr027b, htr079a, htr279a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hc238xy, htr023a, htr028b, htr089a, htr289a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc234xy, hc789xy, htr123a, htr127a, htr246a, htr279a, htr467a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc356zy, htr237c, htr278a, htr367c, htr567a, htr678a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd01a, hd89b, htr012a, htr127a, htr278a, htr789a]
                    ·
                      linarith only [hlam, hd01a, hd78b, htr012a, htr128a, htr289a, htr789a]
                  ·
                    rcases m.htr 4 6 10 (by decide) (by decide) with
                      ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                    ·
                      have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                        linarith only [hlam, hc056zy, htr0610a, htr4610a, htr467a, htr567a])
                      obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, htr0610b, htr067c, htr0710c])
                      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, htr0610b, htr068c, htr0810c])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                        linarith only [hlam, hc237xy, htr023a, htr027b, htr0710a, htr2710a])
                      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                        linarith only [hlam, hc238xy, htr023a, htr028b, htr0810a, htr2810a])
                      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc234xy, hc7810xy, htr123a, htr127a, htr246a, htr2710a, htr467a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                        linarith only [hlam, hc356zy, htr237c, htr278a, htr367c, htr567a, htr678a])
                      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                      rcases m.htr 7 8 10 (by decide) (by decide) with
                        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      ·
                        linarith only [hlam, hd01a, hd810b, htr012a, htr127a, htr278a, htr7810a]
                      ·
                        linarith only [hlam, hd01a, hd78b, htr012a, htr128a, htr2810a, htr7810a]
                    ·
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                          linarith only [hlam, hc356zy, htr237c, htr278a, htr367c, htr567a, htr678a])
                        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                          linarith only [hlam, hc234xy, hc789yx, htr123a, htr127a, htr246a, htr278a, htr467a, htr679a])
                        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc356zy, htr237c, htr279a, htr367c, htr567a, htr679a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc234xy, hc789zy, htr123a, htr127a, htr245a, htr279a, htr458a, htr589a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc234xy, hc578yz, htr123a, htr127a, htr245a, htr278a, htr458c, htr489a, htr589a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                          linarith only [hlam, hc256zy, htr268c, htr289a, htr468b, htr489a, htr568a])
                        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd01a, hd89b, htr012a, htr127a, htr278a, htr789a]
                        ·
                          linarith only [hlam, hd01a, hd78b, htr012a, htr128a, htr289a, htr789a]
                      ·
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc234xy, hc789xy, htr123a, htr127a, htr246a, htr279a, htr467a, htr678a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hc356zy, htr237c, htr279a, htr367c, htr467b, htr479a, htr567a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hd34b, hd78a, htr345a, htr457c, htr479a, htr578a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                          linarith only [hlam, hc234xy, hc789yz, htr123a, htr128a, htr245a, htr289a, htr457a, htr579a])
                        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc256zy, htr268c, htr289a, htr568a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd34b, hd78a, htr346a, htr468a, htr689a, htr789a]
                        ·
                          linarith only [hlam, hd34b, hd89a, htr346a, htr467a, htr678a, htr789a]
          ·
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hc234xy, hc678xy, htr123a, htr126a, htr245a, htr268a, htr456a, htr567a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr269a, htr269b, htr269c, _, _⟩
              linarith only [hlam, hc234xy, hc679xy, htr123a, htr126a, htr245a, htr269a, htr456a, htr567a])
            obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd34b, hd78a, htr345a, htr456a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hd34b, hd79a, htr345a, htr456a, htr567a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc267zy, htr278a, htr567a, htr568a, htr678c])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd34b, hd67a, htr346a, htr468a, htr567a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd01a, hd89b, htr012a, htr127a, htr278a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd67a, hd78b, htr567a, htr568a, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc678xy, htr567a, htr568b, htr589a, htr689a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hc234xy, hc789zy, htr123a, htr127a, htr245a, htr279a, htr458a, htr589a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                linarith only [hlam, hc234xy, hc8910xy, htr123a, htr128a, htr245a, htr2810a, htr458a, htr589a])
              obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hc267zy, htr279a, htr456b, htr469a, htr567a, htr679c])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd28b, hd67a, htr2810a, htr567a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                linarith only [hlam, hc678xy, htr567a, htr568b, htr5810a, htr6810a])
              obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
              have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                linarith only [hlam, hc234xy, hc8910yz, htr123a, htr129a, htr245a, htr2910a, htr458a, htr5810a])
              obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd26b, hd910a, htr268a, htr468a, htr469a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc267zy, htr279c, htr2910a, htr679a, htr7910a]
              ·
                linarith only [hlam, hc267zy, htr279a, htr679b, htr6910a, htr7910a]
            ·
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc234xy, hc678yz, htr123a, htr127a, htr245a, htr278a, htr456a, htr568a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd34b, hd89a, htr345a, htr456a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd34b, hd810a, htr345a, htr456a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc267zy, htr278a, htr678b, htr689a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc267zy, htr278c, htr289a, htr678a, htr789a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                linarith only [hlam, hc234xy, hc689yz, htr123a, htr128a, htr245a, htr289a, htr456a, htr569a])
              obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc267zy, htr278a, htr678b, htr6810a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                linarith only [hlam, hc267zy, htr278c, htr2810a, htr678a, htr7810a])
              obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
              have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                linarith only [hlam, hc234xy, hc8910zy, htr123a, htr128a, htr245a, htr2810a, htr459a, htr5910a])
              obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc236xy, hc589yz, htr123a, htr128a, htr269a, htr289a, htr5910a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd01a, hd910b, htr012a, htr128a, htr289a, htr8910a]
              ·
                linarith only [hlam, hd67a, hd89b, htr567a, htr569a, htr6910a, htr8910a]

theorem shard_074 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr028b : m.d 0 2 < m.d 0 8)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr056c : m.d 0 6 < m.d 0 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False :=
  proof_shard_074 m htr012a htr013a htr023a htr026b htr027b htr028b htr036c htr045a htr046b htr056c htr123a htr125a htr126a htr127a htr128a htr129a htr136a htr235c htr236c htr237c htr245a htr246a htr345a htr346a htr356c htr456a htr456b htr456c

#print axioms shard_074
end Jsp404.NoSatElevenDBMTerminal
