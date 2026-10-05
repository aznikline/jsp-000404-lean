import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_623 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr358a : m.d 3 5 + lam ≤ m.d 5 8)
    (htr358c : m.d 3 8 < m.d 5 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
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
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc389xy, hc389yx, hc389yz, hc389zy⟩ := endpoint_caps m 3 8 9 (by decide) (by decide)
  obtain ⟨hc3910xy, hc3910yx, hc3910yz, hc3910zy⟩ := endpoint_caps m 3 9 10 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd01b, hd67a, htr012a, htr123a, htr236a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd01b, hd68a, htr012a, htr123a, htr236a, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hd01b, hd69a, htr012a, htr123a, htr236a, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, hd01b, hd610a, htr012a, htr123a, htr236a, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc345yz, htr235a, htr237a, htr357c, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc346yz, htr236a, htr237a, htr367c, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hc356yz, htr236a, htr237a, htr367c, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hd35a, hd67b, htr358a, htr456a, htr458a, htr567a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd34a, hd78b, htr345a, htr456a, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr378a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc347xy, htr234a, htr237b, htr278a, htr378a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd34a, hd79b, htr345a, htr456a, htr567a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr379a, htr679a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc347xy, htr234a, htr237b, htr279a, htr379a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd01b, hd910a, htr012a, htr127a, htr279a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc014yx, hc678zy, htr012a, htr045a, htr127a, htr278a, htr456a, htr568a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr045a, htr046a, htr345a, htr467a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc034zy, htr046a, htr346b, htr369a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr346a, htr469a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd34a, hd89b, htr345a, htr456a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd34a, hd910b, htr345a, htr456a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
      ·
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr346a, htr468a, htr567a, htr568a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc034zy, htr046a, htr346b, htr368a, htr468a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr045a, htr046a, htr345a, htr467a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc014yx, hc789yz, htr012a, htr045a, htr127a, htr279a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc356yz, htr368a, htr568c, htr589a, htr689a]
        ·
          linarith only [hlam, hd67b, hd78a, htr567a, htr568a, htr689a, htr789a]
    ·
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc034zy, htr045a, htr345b, htr356a, htr456a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hd34a, hd57b, htr045a, htr046a, htr346a, htr457a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd35a, hd67b, htr356a, htr467a, htr468a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc345yz, htr356b, htr369a, htr456a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hd35a, hd67b, htr356a, htr467a, htr469a, htr569a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd35a, hd78b, htr356a, htr456a, htr457a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd34a, hd57b, htr234a, htr237a, htr378a, htr578a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc347xy, htr234a, htr237b, htr278a, htr378a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd35a, hd79b, htr356a, htr456a, htr457a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hd34a, hd57b, htr234a, htr237a, htr379a, htr579a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc347xy, htr234a, htr237b, htr279a, htr379a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hd35a, hd710b, htr356a, htr456a, htr457a, htr5710a])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
        linarith only [hlam, hd34a, hd57b, htr234a, htr237a, htr3710a, htr5710a])
      obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hc347xy, htr234a, htr237b, htr2710a, htr3710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc014yx, hc789yz, htr012a, htr046a, htr127a, htr279a, htr468a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc014yx, hc7910yz, htr012a, htr046a, htr127a, htr2710a, htr469a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd01b, hd910a, htr012a, htr127a, htr279a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
      ·
        linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
  ·
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr012a, htr123a, htr237a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd01b, hd79a, htr012a, htr123a, htr237a, htr379a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
      linarith only [hlam, hd01b, hd710a, htr012a, htr123a, htr237a, htr3710a])
    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
    rcases m.htr 2 3 8 (by decide) (by decide) with
      ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
    ·
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc345yz, htr235a, htr238a, htr358c, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc346yz, htr236a, htr238a, htr368c, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc356yz, htr236a, htr238a, htr368c, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc357yz, htr237a, htr238a, htr378c, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc367yz, htr237a, htr238a, htr378c, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 4 5 6 (by decide) (by decide) with
        ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
      ·
        have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr457a, htr457b, htr457c, _, _⟩
          linarith only [hlam, hd35a, hd68b, htr357a, htr456a, htr457a, htr568a])
        obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd34a, hd78b, htr345a, htr456a, htr567a, htr678a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd34a, hd68b, htr346a, htr467a, htr567a, htr568a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc034zy, htr046a, htr346b, htr367a, htr467a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hd34a, hd68b, htr045a, htr046a, htr345a, htr468a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc356yz, htr367b, htr379a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd36a, hd78b, htr367a, htr578a, htr579a, htr679a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc014yx, hc789zy, htr012a, htr045a, htr128a, htr289a, htr457a, htr579a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc348xy, htr234a, htr238b, htr289a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd34a, hd89b, htr345a, htr456a, htr568a, htr678c, htr789a]
        ·
          linarith only [hlam, hd34a, hd78b, htr234a, htr238a, htr389a, htr789a]
      ·
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc034zy, htr045a, htr345b, htr356a, htr456a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hd34a, hd58b, htr045a, htr046a, htr346a, htr458a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr457a, htr457b, htr457c, _, _⟩
          linarith only [hlam, hd35a, hd78b, htr356a, htr456a, htr457a, htr578a])
        obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd35a, hd68b, htr356a, htr467a, htr468a, htr567a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc345yz, htr357b, htr379a, htr457a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd35a, hd89b, htr356a, htr456a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd34a, hd58b, htr234a, htr238a, htr389a, htr589a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc348xy, htr234a, htr238b, htr289a, htr389a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc014yx, hc789zy, htr012a, htr046a, htr128a, htr289a, htr467a, htr679a]
        ·
          linarith only [hlam, hd35a, hd78b, htr357a, htr579a, htr678a, htr679a]
    ·
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr012a, htr123a, htr238a, htr389a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
        linarith only [hlam, hd01b, hd810a, htr012a, htr123a, htr238a, htr3810a])
      obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
      rcases m.htr 2 3 9 (by decide) (by decide) with
        ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
      ·
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc356yz, htr236a, htr239a, htr369c, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc357yz, htr237a, htr239a, htr379c, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc367yz, htr237a, htr239a, htr379c, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc378yz, htr238a, htr239a, htr389c, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 4 5 6 (by decide) (by decide) with
          ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
        ·
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hd35a, hd69b, htr357a, htr456a, htr457a, htr569a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hd34a, hd79b, htr345a, htr456a, htr567a, htr679a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd34a, hd89b, htr345a, htr457a, htr578a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd36a, hd79b, htr367a, htr578a, htr579a, htr678a]
          ·
            linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a]
        ·
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hd35a, hd79b, htr356a, htr456a, htr457a, htr579a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd35a, hd89b, htr356a, htr567a, htr678a, htr789a]
          ·
            linarith only [hlam, hd35a, hd79b, htr357a, htr578a, htr678a, htr679a]
      ·
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hd01b, hd910a, htr012a, htr123a, htr239a, htr3910a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        rcases m.htr 2 3 10 (by decide) (by decide) with
          ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
        ·
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, hc356yz, htr2310a, htr236a, htr3610c, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hc357yz, htr2310a, htr237a, htr3710c, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc367yz, htr2310a, htr237a, htr3710c, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc378yz, htr2310a, htr238a, htr3810c, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          rcases m.htr 4 5 6 (by decide) (by decide) with
            ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
          ·
            have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr457a, htr457b, htr457c, _, _⟩
              linarith only [hlam, hd35a, hd610b, htr357a, htr456a, htr457a, htr5610a])
            obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd34a, hd710b, htr345a, htr456a, htr567a, htr6710a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd34a, hd810b, htr345a, htr457a, htr578a, htr7810a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd36a, hd710b, htr367a, htr5710a, htr578a, htr678a]
            ·
              linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a]
          ·
            have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr457a, htr457b, htr457c, _, _⟩
              linarith only [hlam, hd35a, hd710b, htr356a, htr456a, htr457a, htr5710a])
            obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd35a, hd810b, htr356a, htr567a, htr678a, htr7810a]
            ·
              linarith only [hlam, hd35a, hd710b, htr357a, htr578a, htr6710a, htr678a]
        ·
          rcases m.htr 4 5 6 (by decide) (by decide) with
            ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
          ·
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hc014yx, hc367yz, htr012a, htr045a, htr123a, htr237a, htr456a, htr567a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                linarith only [hlam, hd34a, hd67b, htr045a, htr046a, htr345a, htr456c, htr567a])
              obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hc034zy, htr046a, htr346b, htr368a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd34a, hd67b, htr346a, htr468a, htr567a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd34a, hd78b, htr345a, htr456a, htr567a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd34a, hd89b, htr345a, htr456a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a]
              ·
                linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a]
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc035zy, htr056a, htr356b, htr367a, htr567a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc356yz, htr056a, htr057a, htr367a, htr567b])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                linarith only [hlam, hc356yz, htr367a, htr456a, htr457a, htr567b])
              obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc356yz, htr367a, htr457c, htr478a, htr567c, htr678a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hc014yx, hc378yz, htr012a, htr045a, htr123a, htr238a, htr457a, htr578a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hd34a, hd78b, htr045a, htr047a, htr345a, htr478a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc034zy, htr047a, htr347b, htr379a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd34a, hd78b, htr347a, htr479a, htr578a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc015yx, hc389yz, htr012a, htr057a, htr123a, htr239a, htr578a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc015yx, hc3910yz, htr012a, htr057a, htr123a, htr2310a, htr579a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc378yz, htr389a, htr789c, htr7910a, htr8910a]
              ·
                linarith only [hlam, hc378yz, htr389b, htr3910a, htr789a, htr8910a]
          ·
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc034zy, htr045a, htr345b, htr356a, htr456a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc345yz, htr045a, htr046a, htr356a, htr456b])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hc014yx, hc378yz, htr012a, htr046a, htr123a, htr238a, htr467a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc014yx, hc389yz, htr012a, htr046a, htr123a, htr239a, htr468a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a]
            ·
              linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a]

theorem shard_623 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr356b : m.d 3 5 < m.d 3 6)
    (htr357a : m.d 3 5 + lam ≤ m.d 5 7)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr358a : m.d 3 5 + lam ≤ m.d 5 8)
    (htr358c : m.d 3 8 < m.d 5 8)
    : False :=
  proof_shard_623 m htr012a htr123a htr127a htr128a htr234a htr235a htr236a htr345a htr345b htr346a htr346b htr347a htr347b htr356a htr356b htr357a htr357b htr357c htr358a htr358c

#print axioms shard_623
end Jsp404.NoSatElevenDBMTerminal
