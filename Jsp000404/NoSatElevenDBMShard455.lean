import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_455 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr046a : m.d 0 4 + lam ≤ m.d 4 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr056a : m.d 0 5 + lam ≤ m.d 5 6)
    (htr056c : m.d 0 6 < m.d 5 6)
    (htr057a : m.d 0 5 + lam ≤ m.d 5 7)
    (htr057c : m.d 0 7 < m.d 5 7)
    (htr058a : m.d 0 5 + lam ≤ m.d 5 8)
    (htr058b : m.d 0 5 < m.d 0 8)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr459c : m.d 4 9 < m.d 5 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < 4*lam := by
    linarith only [hd03braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
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
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
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
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc457xy, htr034a, htr037a, htr345a, htr347c])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc456xy, htr046a, htr047a, htr345a, htr347a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, htr134c, htr147a, htr347a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc456xy, htr246a, htr247a, htr345a, htr347a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  rcases m.htr 3 4 8 (by decide) (by decide) with
    ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
  ·
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc458xy, htr034a, htr038a, htr345a, htr348c])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc456xy, htr046a, htr048a, htr345a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, htr134c, htr148a, htr348a])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr248a, htr248b, htr248c, _, _⟩
      linarith only [hlam, hc456xy, htr246a, htr248a, htr345a, htr348a])
    obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
    rcases m.htr 3 4 9 (by decide) (by decide) with
      ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
    ·
      have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr039a, htr039b, htr039c, _, _⟩
        linarith only [hlam, hc459xy, htr034a, htr039a, htr345a, htr349c])
      obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
      have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr149a, htr149b, htr149c, _, _⟩
        linarith only [hlam, htr134c, htr149a, htr349a])
      obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
      rcases m.htr 3 4 10 (by decide) (by decide) with
        ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
      ·
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd13a, hd78b, htr035b, htr056a, htr135a, htr567a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd13a, hd67b, htr134a, htr347a, htr478a, htr678a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc457xy, htr145a, htr147b, htr178a, htr478a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hd13a, hd79b, htr035b, htr056a, htr135a, htr567a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd13a, hd67b, htr134a, htr347a, htr479a, htr679a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hc457xy, htr145a, htr147b, htr179a, htr479a])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          rcases m.htr 5 6 8 (by decide) (by decide) with
            ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
          ·
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hd13a, hd89b, htr035b, htr056a, htr135a, htr568a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hd13a, hd68b, htr134a, htr348a, htr489a, htr689a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
              linarith only [hlam, hc458xy, htr145a, htr148b, htr189a, htr489a])
            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
            have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
              linarith only [hlam, hd13a, hd810b, htr035b, htr056a, htr135a, htr568a, htr6810a])
            obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
            have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
              linarith only [hlam, hd13a, hd68b, htr134a, htr348a, htr4810a, htr6810a])
            obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
              linarith only [hlam, hc458xy, htr145a, htr148b, htr1810a, htr4810a])
            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc012yx, hc678zy, htr018a, htr025a, htr189a, htr256a, htr568a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr469a, htr469b, htr469c, _, _⟩
              linarith only [hlam, hc012yx, hc689zy, htr017a, htr024a, htr178a, htr246a, htr469a, htr789a])
            obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc012yx, hc678zy, htr018a, htr025a, htr1810a, htr256a, htr568a, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hc013zy, hc8910yz, htr037a, htr134a, htr137c, htr178a, htr349a, htr4910a, htr7810a])
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
              linarith only [hlam, hd01b, hd910a, htr017a, htr178a, htr789a, htr8910a]
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hd13a, hd67b, htr036b, htr068a, htr134a, htr346b, htr567a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr145a, htr146b, htr168a, htr567a, htr568a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
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
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, htr016b, htr056c, htr169a, htr569a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc458xy, htr038b, htr089a, htr345a, htr348b, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc013zy, hc8910yx, htr036a, htr134a, htr136c, htr168a, htr348a, htr489a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hc678yx, htr458c, htr4810a, htr567a, htr568c, htr6810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd13a, hd910b, htr035b, htr056a, htr135a, htr569a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc689xy, htr168a, htr169b, htr1910a, htr6910a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc012yx, hc679zy, htr019a, htr025a, htr1910a, htr256a, htr569a, htr7910a]
              ·
                linarith only [hlam, hc013zy, hc8910zy, htr037a, htr134a, htr137c, htr179a, htr348a, htr4810a, htr7910a]
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc678yx, htr068a, htr069a, htr567a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc678yx, htr168a, htr169a, htr567a, htr569a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
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
                  linarith only [hlam, hc458xy, htr038b, htr0810a, htr345a, htr348b, htr4810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc459xy, htr039b, htr0910a, htr345a, htr349b, htr4910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc013zy, hc8910xy, htr036a, htr134a, htr136c, htr168a, htr348a, htr4810a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc678yx, htr458c, htr489a, htr567a, htr568c, htr689a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd13a, hd910b, htr134a, htr348a, htr489a, htr8910a]
                ·
                  linarith only [hlam, hd13a, hd89b, htr134a, htr349a, htr4910a, htr8910a]
              ·
                rcases m.htr 5 8 9 (by decide) (by decide) with
                  ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
                ·
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc013zy, hc8910yx, htr035b, htr036a, htr058a, htr135a, htr136c, htr168a, htr589a, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc678yx, htr458c, htr4810a, htr567a, htr568c, htr6810a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc013zy, hc8910zy, htr036a, htr134a, htr136c, htr169a, htr348a, htr4810a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc679yx, htr459c, htr4910a, htr567a, htr569c, htr6910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd13a, hd910b, htr035b, htr058a, htr135a, htr589a, htr8910a]
                  ·
                    linarith only [hlam, hd13a, hd89b, htr134a, htr349a, htr4910a, htr8910a]
                ·
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc678yx, htr567a, htr568c, htr589a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc013zy, hc8910xy, htr036a, htr134a, htr136c, htr168a, htr348a, htr4810a, htr689a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc678yx, htr458c, htr4810a, htr567a, htr568c, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc013zy, hc8910yz, htr036a, htr134a, htr136c, htr168a, htr349a, htr4910a, htr6810a])
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
            linarith only [hlam, hd13a, hd56b, htr134a, htr346a, htr467a, htr567a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc456xy, htr036b, htr067a, htr345a, htr346b, htr467a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc456xy, htr145a, htr146b, htr167a, htr467a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 3 6 8 (by decide) (by decide) with
            ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc013zy, htr036c, htr068a, htr134a, htr346b, htr368a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr067c, htr068b, htr078c])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, htr136c, htr168a, htr368a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc457xy, htr037b, htr078a, htr345a, htr347b, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hc013zy, hc789yx, htr036a, htr134a, htr136c, htr167a, htr347a, htr478a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc678xy, htr467c, htr468a, htr479a, htr679a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc013zy, hc7810yx, htr036a, htr134a, htr136c, htr167a, htr347a, htr478a, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hc678xy, htr467c, htr468a, htr4710a, htr6710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hd13a, hd89b, htr134a, htr346a, htr468a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
              linarith only [hlam, hc678xy, htr167a, htr168b, htr189a, htr689a])
            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hd13a, hd910b, htr134a, htr347a, htr479a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hd13a, hd79b, htr134a, htr349a, htr4910a, htr7910a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
              linarith only [hlam, hc459xy, htr145a, htr149b, htr1910a, htr4910a])
            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hc012yx, hc789zy, htr019a, htr024a, htr1910a, htr247a, htr479a, htr8910a]
            ·
              linarith only [hlam, hc012yx, hc7910zy, htr018a, htr024a, htr189a, htr247a, htr4710a, htr8910a]
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr036b, htr068a, htr368a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            rcases m.htr 3 6 9 (by decide) (by decide) with
              ⟨htr369a, htr369b, htr369c, _, _⟩ | ⟨htr369a, htr369b, htr369c, _, _⟩
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc013zy, htr036c, htr069a, htr134a, htr346b, htr369a])
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
                linarith only [hlam, hc457xy, htr037b, htr079a, htr345a, htr347b, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc458xy, htr038b, htr089a, htr345a, htr348b, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc013zy, hc789xy, htr036a, htr134a, htr136c, htr167a, htr347a, htr479a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc679xy, htr467c, htr469a, htr478a, htr678a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd13a, hd89b, htr134a, htr347a, htr478a, htr789a]
              ·
                linarith only [hlam, hd13a, hd78b, htr134a, htr348a, htr489a, htr789a]
            ·
              rcases m.htr 3 6 10 (by decide) (by decide) with
                ⟨htr3610a, htr3610b, htr3610c, _, _⟩ | ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, hc013zy, htr036c, htr0610a, htr134a, htr346b, htr3610a])
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
                  linarith only [hlam, hc457xy, htr037b, htr0710a, htr345a, htr347b, htr4710a])
                obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc458xy, htr038b, htr0810a, htr345a, htr348b, htr4810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc013zy, hc7810xy, htr036a, htr134a, htr136c, htr167a, htr347a, htr4710a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc6710xy, htr4610a, htr467c, htr478a, htr678a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 7 8 10 (by decide) (by decide) with
                  ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                ·
                  linarith only [hlam, hd13a, hd810b, htr134a, htr347a, htr478a, htr7810a]
                ·
                  linarith only [hlam, hd13a, hd78b, htr134a, htr348a, htr4810a, htr7810a]
              ·
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  rcases m.htr 5 7 8 (by decide) (by decide) with
                    ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                  ·
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd13a, hd89b, htr035b, htr057a, htr135a, htr578a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hd13a, hd78b, htr134a, htr348a, htr489a, htr789a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc458xy, htr145a, htr148b, htr189a, htr489a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hc012yx, hc678yz, htr018a, htr025a, htr189a, htr257a, htr578a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hc013zy, hc789zy, htr036a, htr134a, htr347a, htr368a, htr479a, htr689a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                      linarith only [hlam, hc013zy, hc8910xy, htr036a, htr134a, htr348a, htr368a, htr4810a, htr689a])
                    obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hc458xy, htr145a, htr148b, htr1810a, htr4810a])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc012yx, hc678yz, htr018a, htr025a, htr1810a, htr257a, htr578a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                      linarith only [hlam, hc013zy, hc8910yz, htr036a, htr134a, htr349a, htr368a, htr4910a, htr6810a])
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
                      linarith only [hlam, hd03b, hd910a, htr036a, htr368a, htr689a, htr8910a]
                  ·
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hd13a, hd57b, htr134a, htr347a, htr478a, htr578a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hc457xy, htr037b, htr078a, htr345a, htr347b, htr478a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc457xy, htr145a, htr147b, htr178a, htr478a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hd01b, hd79a, htr017a, htr178a, htr678a, htr679a])
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
                      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                        linarith only [hlam, htr017b, htr057c, htr179a, htr579a])
                      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc458xy, htr038b, htr089a, htr345a, htr348b, htr489a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                        linarith only [hlam, hc013zy, hc8910yx, htr037a, htr134a, htr137c, htr178a, htr348a, htr489a, htr7810a])
                      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                        linarith only [hlam, hc567zy, htr458c, htr4810a, htr578c, htr678a, htr7810a])
                      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                        linarith only [hlam, hc013zy, hc8910zy, htr036a, htr134a, htr348a, htr369a, htr4810a, htr6910a])
                      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                        linarith only [hlam, hc012yx, hc679yz, htr019a, htr025a, htr1910a, htr257a, htr579a, htr6910a])
                      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd13a, hd910b, htr134a, htr348a, htr489a, htr8910a]
                      ·
                        linarith only [hlam, hd67a, hd89b, htr178a, htr179b, htr1910a, htr678a, htr8910a]
                    ·
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, hc567zy, htr078a, htr079a, htr579a, htr678a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                        linarith only [hlam, hc567zy, htr178a, htr179a, htr579a, htr678a])
                      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
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
                          linarith only [hlam, hc458xy, htr038b, htr0810a, htr345a, htr348b, htr4810a])
                        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                          linarith only [hlam, hc459xy, htr039b, htr0910a, htr345a, htr349b, htr4910a])
                        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                          linarith only [hlam, hc013zy, hc8910xy, htr037a, htr134a, htr137c, htr178a, htr348a, htr4810a, htr789a])
                        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc567zy, htr458c, htr489a, htr578c, htr678a, htr789a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd13a, hd910b, htr134a, htr348a, htr489a, htr8910a]
                        ·
                          linarith only [hlam, hd13a, hd89b, htr134a, htr349a, htr4910a, htr8910a]
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
                            linarith only [hlam, hc013zy, hc8910yx, htr037a, htr134a, htr137c, htr178a, htr348a, htr489a, htr7810a])
                          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                            linarith only [hlam, hc567zy, htr458c, htr4810a, htr578c, htr678a, htr7810a])
                          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                            linarith only [hlam, hc013zy, hc8910zy, htr036a, htr134a, htr348a, htr369a, htr4810a, htr6910a])
                          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                            linarith only [hlam, hc012yx, hc689yz, htr019a, htr024a, htr1910a, htr248a, htr489a, htr6910a])
                          obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                            linarith only [hlam, hc459xy, htr145a, htr149b, htr1910a, htr4910a])
                          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd13a, hd910b, htr134a, htr348a, htr489a, htr8910a]
                          ·
                            linarith only [hlam, hd13a, hd89b, htr134a, htr349a, htr4910a, htr8910a]
                        ·
                          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                            linarith only [hlam, hc013zy, hc8910xy, htr037a, htr134a, htr137c, htr178a, htr348a, htr4810a, htr789a])
                          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                          have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                            linarith only [hlam, hc458xy, htr145a, htr148b, htr1810a, htr4810a])
                          obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                            linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
                          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                            linarith only [hlam, hd01b, hd89a, htr018a, htr1810a, htr6810a, htr689a])
                          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                            linarith only [hlam, hc013zy, hc8910yz, htr036a, htr134a, htr349a, htr368a, htr4910a, htr6810a])
                          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                            linarith only [hlam, hc567zy, htr459c, htr4910a, htr579c, htr679a, htr7910a])
                          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd01b, hd89a, htr017a, htr179a, htr7910a, htr8910a]
                          ·
                            linarith only [hlam, hd01b, hd910a, htr017a, htr178a, htr789a, htr8910a]
                ·
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc013zy, hc789xy, htr036a, htr134a, htr136c, htr167a, htr347a, htr479a, htr678a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc457xy, htr145a, htr147b, htr179a, htr479a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc013zy, hc7810xy, htr036a, htr134a, htr136c, htr167a, htr347a, htr4710a, htr678a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                    linarith only [hlam, hc457xy, htr145a, htr147b, htr1710a, htr4710a])
                  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd01b, hd78a, htr017a, htr179a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc013zy, hc789yz, htr036a, htr134a, htr136c, htr167a, htr348a, htr489a, htr679a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc458xy, htr145a, htr148b, htr189a, htr489a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd01b, hd78a, htr017a, htr1710a, htr6710a, htr678a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc013zy, hc7910yz, htr036a, htr134a, htr136c, htr167a, htr349a, htr4910a, htr6710a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd01b, hd89a, htr016a, htr167a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd01b, hd910a, htr016a, htr167a, htr679a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hd01b, hd79a, htr018a, htr189a, htr7910a, htr8910a]
      ·
        have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
          linarith only [hlam, htr034b, htr0410a, htr3410a])
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
          linarith only [hlam, htr046c, htr0610a, htr4610a])
        obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc6710yx, htr034b, htr046a, htr3410a, htr4610b, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc456xy, htr145a, htr146b, htr167a, htr467a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, htr047c, htr0710a, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc7810yx, htr034b, htr047a, htr3410a, htr4710b, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc457xy, htr145a, htr147b, htr178a, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, htr048c, htr0810a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          linarith only [hlam, hc467zy, htr3410a, htr347a, htr4710b, htr6710a])
        obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd01b, hd710a, htr017a, htr178a, htr6710a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc478zy, htr3410a, htr348a, htr4810b, htr7810a]
        ·
          linarith only [hlam, hd01b, hd810a, htr016a, htr167a, htr678a, htr7810a]
    ·
      have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr049a, htr049b, htr049c, _, _⟩
        linarith only [hlam, htr034b, htr049a, htr349a])
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
        linarith only [hlam, htr046c, htr069a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc679yx, htr034b, htr046a, htr349a, htr467a, htr469b])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc456xy, htr145a, htr146b, htr167a, htr467a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, htr047c, htr079a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc789yx, htr034b, htr047a, htr349a, htr478a, htr479b])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc457xy, htr145a, htr147b, htr178a, htr478a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, htr048c, htr089a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc467zy, htr347a, htr349a, htr479b, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd01b, hd79a, htr017a, htr178a, htr678a, htr679a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc478zy, htr348a, htr349a, htr489b, htr789a]
      ·
        linarith only [hlam, hd01b, hd89a, htr016a, htr167a, htr678a, htr789a]
  ·
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, htr034b, htr048a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr046b, htr048c, htr068b])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, htr047b, htr048c, htr078b])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, htr046c, htr068a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc678yx, htr034b, htr046a, htr348a, htr467a, htr468b])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc456xy, htr145a, htr146b, htr167a, htr467a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, htr047c, htr078a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hc789xy, htr034b, htr047a, htr348a, htr478b, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hc457xy, htr145a, htr147b, htr179a, htr479a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hc467zy, htr347a, htr348a, htr478b, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr017a, htr179a, htr678a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hc013zy, hc789yz, htr035b, htr036a, htr058a, htr135a, htr136c, htr167a, htr589a, htr679a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
      linarith only [hlam, hc013zy, hc578zy, htr035b, htr036a, htr058b, htr089a, htr135a, htr136c, htr167a, htr589a, htr678a])
    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc468yx, htr046a, htr048c, htr089a, htr489a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd23b, hd78a, htr234a, htr348a, htr489a, htr789a]
    ·
      linarith only [hlam, hd01b, hd89a, htr016a, htr167a, htr678a, htr789a]

theorem shard_455 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr046a : m.d 0 4 + lam ≤ m.d 4 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr056a : m.d 0 5 + lam ≤ m.d 5 6)
    (htr056c : m.d 0 6 < m.d 5 6)
    (htr057a : m.d 0 5 + lam ≤ m.d 5 7)
    (htr057c : m.d 0 7 < m.d 5 7)
    (htr058a : m.d 0 5 + lam ≤ m.d 5 8)
    (htr058b : m.d 0 5 < m.d 0 8)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347b : m.d 3 4 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr456c : m.d 4 6 < m.d 5 6)
    (htr457c : m.d 4 7 < m.d 5 7)
    (htr458c : m.d 4 8 < m.d 5 8)
    (htr459c : m.d 4 9 < m.d 5 9)
    : False :=
  proof_shard_455 m htr016a htr016b htr017a htr017b htr018a htr019a htr024a htr025a htr034a htr034b htr035b htr036a htr036b htr036c htr046a htr046b htr046c htr056a htr056c htr057a htr057c htr058a htr058b htr134a htr134c htr135a htr136c htr137c htr145a htr146b htr234a htr246a htr256a htr257a htr345a htr346a htr346b htr347a htr347b htr347c htr456c htr457c htr458c htr459c

#print axioms shard_455
end Jsp404.NoSatElevenDBMTerminal
