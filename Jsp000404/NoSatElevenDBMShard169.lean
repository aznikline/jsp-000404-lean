import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_169 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr037c : m.d 0 7 < m.d 3 7)
    (htr038c : m.d 0 8 < m.d 3 8)
    (htr039c : m.d 0 9 < m.d 3 9)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr056c : m.d 0 6 < m.d 5 6)
    (htr057c : m.d 0 7 < m.d 5 7)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr156a : m.d 1 5 + lam ≤ m.d 5 6)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr158a : m.d 1 5 + lam ≤ m.d 5 8)
    (htr158b : m.d 1 5 < m.d 1 8)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr459c : m.d 4 9 < m.d 5 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
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
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr034c, htr047a, htr347a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, hc457xy, htr134a, htr137a, htr345a, htr347c])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, hc456xy, htr146a, htr147a, htr345a, htr347a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  rcases m.htr 3 4 8 (by decide) (by decide) with
    ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
  ·
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, htr034c, htr048a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr138a, htr138b, htr138c, _, _⟩
      linarith only [hlam, hc458xy, htr134a, htr138a, htr345a, htr348c])
    obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
    rcases m.htr 3 4 9 (by decide) (by decide) with
      ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
    ·
      have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr049a, htr049b, htr049c, _, _⟩
        linarith only [hlam, htr034c, htr049a, htr349a])
      obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
      have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr139a, htr139b, htr139c, _, _⟩
        linarith only [hlam, hc459xy, htr134a, htr139a, htr345a, htr349c])
      obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
      rcases m.htr 3 4 10 (by decide) (by decide) with
        ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
      ·
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr234a, htr347a, htr478a, htr678a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc457xy, htr045a, htr047b, htr078a, htr478a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hd01a, hd79b, htr015a, htr156a, htr567a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr234a, htr347a, htr479a, htr679a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, hc457xy, htr045a, htr047b, htr079a, htr479a])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          rcases m.htr 5 6 8 (by decide) (by decide) with
            ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
          ·
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hd01a, hd89b, htr015a, htr156a, htr568a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hd23a, hd68b, htr234a, htr348a, htr489a, htr689a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
              linarith only [hlam, hc458xy, htr045a, htr048b, htr089a, htr489a])
            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
            have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
              linarith only [hlam, hd01a, hd810b, htr015a, htr156a, htr568a, htr6810a])
            obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
            have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
              linarith only [hlam, hd23a, hd68b, htr234a, htr348a, htr4810a, htr6810a])
            obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
            have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
              linarith only [hlam, hc458xy, htr045a, htr048b, htr0810a, htr4810a])
            obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc123zy, hc678zy, htr038c, htr089a, htr135b, htr138a, htr156a, htr235a, htr568a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr469a, htr469b, htr469c, _, _⟩
              linarith only [hlam, hc123zy, hc689zy, htr037c, htr078a, htr137a, htr234a, htr346a, htr469a, htr789a])
            obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc123zy, hc678zy, htr038c, htr0810a, htr135b, htr138a, htr156a, htr235a, htr568a, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hc123zy, hc8910yz, htr037c, htr078a, htr137a, htr234a, htr349a, htr4910a, htr7810a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc679yx, htr456c, htr469c, htr4910a, htr567a, htr6910a])
            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hd67b, hd89a, htr456c, htr469a, htr567a, htr6910a, htr8910a]
            ·
              linarith only [hlam, hd13b, hd910a, htr037c, htr078a, htr137a, htr789a, htr8910a]
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr045a, htr046b, htr068a, htr567a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            rcases m.htr 5 6 9 (by decide) (by decide) with
              ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, htr056c, htr069a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, htr068c, htr069b, htr089c])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc458xy, htr045a, htr048b, htr089a, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc123zy, hc8910yx, htr036c, htr068a, htr136a, htr234a, htr348a, htr489a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hc678yx, htr458c, htr4810a, htr567a, htr568c, htr6810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd01a, hd910b, htr015a, htr156a, htr569a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                linarith only [hlam, hc689xy, htr068a, htr069b, htr0910a, htr6910a])
              obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc123zy, hc679zy, htr039c, htr0910a, htr135b, htr139a, htr156a, htr235a, htr569a, htr7910a]
              ·
                linarith only [hlam, hc123zy, hc8910zy, htr037c, htr079a, htr137a, htr234a, htr348a, htr4810a, htr7910a]
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc678yx, htr068a, htr069a, htr567a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, htr056c, htr0610a, htr5610a])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0610b, htr068c, htr0810c])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                  linarith only [hlam, htr0610b, htr069c, htr0910c])
                obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc458xy, htr045a, htr048b, htr0810a, htr4810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc459xy, htr045a, htr049b, htr0910a, htr4910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc123zy, hc8910xy, htr036c, htr068a, htr136a, htr234a, htr348a, htr4810a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc678yx, htr458c, htr489a, htr567a, htr568c, htr689a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                ·
                  linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
              ·
                rcases m.htr 5 8 9 (by decide) (by decide) with
                  ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
                ·
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910yx, htr036c, htr068a, htr135b, htr136a, htr158a, htr235a, htr589a, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc678yx, htr458c, htr4810a, htr567a, htr568c, htr6810a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910zy, htr036c, htr069a, htr136a, htr234a, htr348a, htr4810a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc679yx, htr459c, htr4910a, htr567a, htr569c, htr6910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd01a, hd910b, htr015a, htr158a, htr589a, htr8910a]
                  ·
                    linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
                ·
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc678yx, htr567a, htr568c, htr589a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910xy, htr036c, htr068a, htr136a, htr234a, htr348a, htr4810a, htr689a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc678yx, htr458c, htr4810a, htr567a, htr568c, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910yz, htr036c, htr068a, htr136a, htr234a, htr349a, htr4910a, htr6810a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc679yx, htr459c, htr4910a, htr567a, htr569c, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd67b, hd89a, htr567a, htr569a, htr6910a, htr8910a]
                  ·
                    linarith only [hlam, hd67b, hd910a, htr567a, htr568a, htr689a, htr8910a]
        ·
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd23a, hd56b, htr234a, htr346a, htr467a, htr567a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc456xy, htr045a, htr046b, htr067a, htr467a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          rcases m.htr 3 6 8 (by decide) (by decide) with
            ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr036c, htr068a, htr368a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr067c, htr068b, htr078c])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc457xy, htr045a, htr047b, htr078a, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hc123zy, hc789yx, htr036c, htr067a, htr136a, htr234a, htr347a, htr478a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc678xy, htr467c, htr468a, htr479a, htr679a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc123zy, hc7810yx, htr036c, htr067a, htr136a, htr234a, htr347a, htr478a, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hc678xy, htr467c, htr468a, htr4710a, htr6710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
              linarith only [hlam, hc678xy, htr067a, htr068b, htr089a, htr689a])
            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hd23a, hd910b, htr234a, htr347a, htr479a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hd23a, hd79b, htr234a, htr349a, htr4910a, htr7910a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
              linarith only [hlam, hc459xy, htr045a, htr049b, htr0910a, htr4910a])
            obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hc123zy, hc789zy, htr039c, htr0910a, htr139a, htr234a, htr347a, htr479a, htr8910a]
            ·
              linarith only [hlam, hc123zy, hc7910zy, htr038c, htr089a, htr138a, htr234a, htr347a, htr4710a, htr8910a]
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc456xy, htr045a, htr046b, htr068a, htr346c, htr368a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            rcases m.htr 3 6 9 (by decide) (by decide) with
              ⟨htr369a, htr369b, htr369c, _, _⟩ | ⟨htr369a, htr369b, htr369c, _, _⟩
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, htr036c, htr069a, htr369a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, htr067c, htr069b, htr079c])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, htr068c, htr069b, htr089c])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hc456xy, htr345a, htr346b, htr369a, htr469a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc457xy, htr045a, htr047b, htr079a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc458xy, htr045a, htr048b, htr089a, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc123zy, hc789xy, htr036c, htr067a, htr136a, htr234a, htr347a, htr479a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc679xy, htr467c, htr469a, htr478a, htr678a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
              ·
                linarith only [hlam, hd23a, hd78b, htr234a, htr348a, htr489a, htr789a]
            ·
              rcases m.htr 3 6 10 (by decide) (by decide) with
                ⟨htr3610a, htr3610b, htr3610c, _, _⟩ | ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, htr036c, htr0610a, htr3610a])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                  linarith only [hlam, htr0610b, htr067c, htr0710c])
                obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0610b, htr068c, htr0810c])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                  linarith only [hlam, hc456xy, htr345a, htr346b, htr3610a, htr4610a])
                obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                  linarith only [hlam, hc457xy, htr045a, htr047b, htr0710a, htr4710a])
                obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc458xy, htr045a, htr048b, htr0810a, htr4810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc123zy, hc7810xy, htr036c, htr067a, htr136a, htr234a, htr347a, htr4710a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc6710xy, htr4610a, htr467c, htr478a, htr678a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 7 8 10 (by decide) (by decide) with
                  ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                ·
                  linarith only [hlam, hd23a, hd810b, htr234a, htr347a, htr478a, htr7810a]
                ·
                  linarith only [hlam, hd23a, hd78b, htr234a, htr348a, htr4810a, htr7810a]
              ·
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  rcases m.htr 5 7 8 (by decide) (by decide) with
                    ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                  ·
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd01a, hd89b, htr015a, htr157a, htr578a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hd23a, hd78b, htr234a, htr348a, htr489a, htr789a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, hc458xy, htr045a, htr048b, htr089a, htr489a])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hc123zy, hc678yz, htr038c, htr089a, htr135b, htr138a, htr157a, htr235a, htr578a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hc123zy, hc789zy, htr136a, htr234a, htr347a, htr368a, htr479a, htr689a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910xy, htr136a, htr234a, htr348a, htr368a, htr4810a, htr689a])
                    obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc458xy, htr045a, htr048b, htr0810a, htr4810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc123zy, hc678yz, htr038c, htr0810a, htr135b, htr138a, htr157a, htr235a, htr578a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910yz, htr136a, htr234a, htr349a, htr368a, htr4910a, htr6810a])
                    obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hc789yx, htr457c, htr479c, htr4910a, htr578a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd78b, hd89a, htr457c, htr479a, htr578a, htr7910a, htr8910a]
                    ·
                      linarith only [hlam, hd13b, hd910a, htr136a, htr368a, htr689a, htr8910a]
                  ·
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hd23a, hd57b, htr234a, htr347a, htr478a, htr578a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hc457xy, htr045a, htr047b, htr078a, htr478a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hd13b, hd79a, htr037c, htr078a, htr137a, htr678a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    rcases m.htr 5 7 9 (by decide) (by decide) with
                      ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                    ·
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, htr057c, htr079a, htr579a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, htr078c, htr079b, htr089c])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc458xy, htr045a, htr048b, htr089a, htr489a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                        linarith only [hlam, hc123zy, hc8910yx, htr037c, htr078a, htr137a, htr234a, htr348a, htr489a, htr7810a])
                      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                        linarith only [hlam, hc567zy, htr458c, htr4810a, htr578c, htr678a, htr7810a])
                      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                        linarith only [hlam, hc123zy, hc8910zy, htr136a, htr234a, htr348a, htr369a, htr4810a, htr6910a])
                      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                      have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                        linarith only [hlam, hc123zy, hc679yz, htr039c, htr0910a, htr135b, htr139a, htr157a, htr235a, htr579a, htr6910a])
                      obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                      ·
                        linarith only [hlam, hd67a, hd89b, htr078a, htr079b, htr0910a, htr678a, htr8910a]
                    ·
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, hc567zy, htr078a, htr079a, htr579a, htr678a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      rcases m.htr 5 7 10 (by decide) (by decide) with
                        ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                      ·
                        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                          linarith only [hlam, htr057c, htr0710a, htr5710a])
                        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, htr0710b, htr078c, htr0810c])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                          linarith only [hlam, htr0710b, htr079c, htr0910c])
                        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                          linarith only [hlam, hc458xy, htr045a, htr048b, htr0810a, htr4810a])
                        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                          linarith only [hlam, hc459xy, htr045a, htr049b, htr0910a, htr4910a])
                        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                          linarith only [hlam, hc123zy, hc8910xy, htr037c, htr078a, htr137a, htr234a, htr348a, htr4810a, htr789a])
                        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc567zy, htr458c, htr489a, htr578c, htr678a, htr789a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                        ·
                          linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
                      ·
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                            linarith only [hlam, hc567zy, htr458c, htr489a, htr578c, htr678a, htr789a])
                          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                            linarith only [hlam, hc123zy, hc8910yx, htr037c, htr078a, htr137a, htr234a, htr348a, htr489a, htr7810a])
                          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                            linarith only [hlam, hc567zy, htr458c, htr4810a, htr578c, htr678a, htr7810a])
                          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                            linarith only [hlam, hc123zy, hc8910zy, htr136a, htr234a, htr348a, htr369a, htr4810a, htr6910a])
                          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                          have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                            linarith only [hlam, hc123zy, hc689yz, htr039c, htr0910a, htr139a, htr234a, htr348a, htr489a, htr6910a])
                          obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                            linarith only [hlam, hc459xy, htr045a, htr049b, htr0910a, htr4910a])
                          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                          ·
                            linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
                        ·
                          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                            linarith only [hlam, hc123zy, hc8910xy, htr037c, htr078a, htr137a, htr234a, htr348a, htr4810a, htr789a])
                          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                            linarith only [hlam, hc458xy, htr045a, htr048b, htr0810a, htr4810a])
                          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                            linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
                          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                            linarith only [hlam, hd13b, hd89a, htr038c, htr0810a, htr138a, htr6810a, htr689a])
                          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                            linarith only [hlam, hc123zy, hc8910yz, htr136a, htr234a, htr349a, htr368a, htr4910a, htr6810a])
                          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                            linarith only [hlam, hc567zy, htr459c, htr4910a, htr579c, htr679a, htr7910a])
                          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd13b, hd89a, htr037c, htr079a, htr137a, htr7910a, htr8910a]
                          ·
                            linarith only [hlam, hd13b, hd910a, htr037c, htr078a, htr137a, htr789a, htr8910a]
                ·
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc123zy, hc789xy, htr036c, htr067a, htr136a, htr234a, htr347a, htr479a, htr678a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, hc457xy, htr045a, htr047b, htr079a, htr479a])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc123zy, hc7810xy, htr036c, htr067a, htr136a, htr234a, htr347a, htr4710a, htr678a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                    linarith only [hlam, hc457xy, htr045a, htr047b, htr0710a, htr4710a])
                  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd13b, hd78a, htr037c, htr079a, htr137a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc123zy, hc789yz, htr036c, htr067a, htr136a, htr234a, htr348a, htr489a, htr679a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, hc458xy, htr045a, htr048b, htr089a, htr489a])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd13b, hd78a, htr037c, htr0710a, htr137a, htr6710a, htr678a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc123zy, hc7910yz, htr036c, htr067a, htr136a, htr234a, htr349a, htr4910a, htr6710a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd13b, hd89a, htr036c, htr067a, htr136a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd13b, hd910a, htr036c, htr067a, htr136a, htr679a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hd13b, hd79a, htr038c, htr089a, htr138a, htr7910a, htr8910a]
      ·
        have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
          linarith only [hlam, hc456xy, htr0410a, htr045a, htr3410a, htr346a])
        obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
        have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
          linarith only [hlam, htr0410c, htr046b, htr0610b])
        obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
          linarith only [hlam, htr0410c, htr047b, htr0710b])
        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
          linarith only [hlam, htr0410c, htr048b, htr0810b])
        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
        have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
          linarith only [hlam, htr036c, htr0610a, htr346c, htr4610a])
        obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc6710yx, htr134b, htr146a, htr3410a, htr4610b, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc456xy, htr045a, htr046b, htr067a, htr467a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, htr037c, htr0710a, htr347c, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc7810yx, htr134b, htr147a, htr3410a, htr4710b, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc457xy, htr045a, htr047b, htr078a, htr478a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, htr038c, htr0810a, htr348c, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          linarith only [hlam, hc467zy, htr3410a, htr347a, htr4710b, htr6710a])
        obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd13b, hd710a, htr037c, htr078a, htr137a, htr6710a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc478zy, htr3410a, htr348a, htr4810b, htr7810a]
        ·
          linarith only [hlam, hd13b, hd810a, htr036c, htr067a, htr136a, htr678a, htr7810a]
    ·
      have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr049a, htr049b, htr049c, _, _⟩
        linarith only [hlam, hc456xy, htr045a, htr049a, htr346a, htr349a])
      obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, htr046b, htr049c, htr069b])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, htr047b, htr049c, htr079b])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
        linarith only [hlam, htr048b, htr049c, htr089b])
      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, htr036c, htr069a, htr346c, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc679yx, htr134b, htr146a, htr349a, htr467a, htr469b])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc456xy, htr045a, htr046b, htr067a, htr467a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, htr037c, htr079a, htr347c, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc789yx, htr134b, htr147a, htr349a, htr478a, htr479b])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc457xy, htr045a, htr047b, htr078a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, htr038c, htr089a, htr348c, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc467zy, htr347a, htr349a, htr479b, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd13b, hd79a, htr037c, htr078a, htr137a, htr678a, htr679a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc478zy, htr348a, htr349a, htr489b, htr789a]
      ·
        linarith only [hlam, hd13b, hd89a, htr036c, htr067a, htr136a, htr678a, htr789a]
  ·
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc456xy, htr045a, htr048a, htr346a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr046b, htr048c, htr068b])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, htr047b, htr048c, htr078b])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, htr134b, htr148a, htr348a])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, htr036c, htr068a, htr346c, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc678yx, htr134b, htr146a, htr348a, htr467a, htr468b])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc456xy, htr045a, htr046b, htr067a, htr467a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, htr037c, htr078a, htr347c, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hc789xy, htr134b, htr147a, htr348a, htr478b, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
      linarith only [hlam, hc457xy, htr045a, htr047b, htr079a, htr479a])
    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hc467zy, htr347a, htr348a, htr478b, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd13b, hd78a, htr037c, htr079a, htr137a, htr678a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hc123zy, hc789yz, htr036c, htr067a, htr135b, htr136a, htr158a, htr235a, htr589a, htr679a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hc123zy, hc578zy, htr036c, htr067a, htr135b, htr136a, htr158b, htr189a, htr235a, htr589a, htr678a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc468yx, htr146a, htr148c, htr189a, htr489a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd13b, hd78a, htr134a, htr348a, htr489a, htr789a]
    ·
      linarith only [hlam, hd13b, hd89a, htr036c, htr067a, htr136a, htr678a, htr789a]

theorem shard_169 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr037c : m.d 0 7 < m.d 3 7)
    (htr038c : m.d 0 8 < m.d 3 8)
    (htr039c : m.d 0 9 < m.d 3 9)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr056c : m.d 0 6 < m.d 5 6)
    (htr057c : m.d 0 7 < m.d 5 7)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr156a : m.d 1 5 + lam ≤ m.d 5 6)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr158a : m.d 1 5 + lam ≤ m.d 5 8)
    (htr158b : m.d 1 5 < m.d 1 8)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr459c : m.d 4 9 < m.d 5 9)
    : False :=
  proof_shard_169 m htr015a htr034c htr036c htr037c htr038c htr039c htr045a htr046b htr056c htr057c htr134a htr134b htr135b htr136a htr146a htr156a htr157a htr158a htr158b htr234a htr235a htr345a htr346a htr346b htr346c htr347a htr347c htr456c htr457c htr458c htr459c

#print axioms shard_169
end Jsp404.NoSatElevenDBMTerminal
