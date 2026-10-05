import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_405 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr358c : m.d 3 8 < m.d 5 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc345yx, htr134b, htr135a, htr146a, htr346a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, hc345yx, htr134b, htr135a, htr147a, htr347a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, hc345yx, htr134b, htr135a, htr148a, htr348a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr023c, htr037a, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr123c, htr137a, htr237a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    rcases m.htr 2 3 8 (by decide) (by decide) with
      ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr023c, htr038a, htr238a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr123c, htr138a, htr238a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      rcases m.htr 2 3 9 (by decide) (by decide) with
        ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
      ·
        rcases m.htr 2 3 10 (by decide) (by decide) with
          ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
        ·
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd12a, hd78b, htr125a, htr256a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd12a, hd67b, htr123a, htr237a, htr378a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc357xy, htr135a, htr137b, htr178a, htr378a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc012yx, hc467yz, htr017a, htr025a, htr178a, htr256a, htr478a, htr567a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hc012yx, hc678zy, htr014a, htr023a, htr147a, htr236a, htr368a, htr478a])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc012yx, hc789xy, htr014a, htr023a, htr147a, htr237a, htr379a, htr478a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc357xy, htr135a, htr137b, htr179a, htr379a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc012yx, hc467yz, htr017a, htr025a, htr179a, htr256a, htr479a, htr567a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hc012yx, hc789yz, htr014a, htr023a, htr147a, htr238a, htr389a, htr479a])
            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc678yx, htr356c, htr368c, htr389a, htr567a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd67b, hd78a, htr356c, htr368a, htr567a, htr689a, htr789a]
            ·
              linarith only [hlam, hd01b, hd89a, htr014a, htr147a, htr478a, htr789a]
          ·
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hd12a, hd56b, htr123a, htr236a, htr367a, htr567a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc356xy, htr013b, htr036b, htr067a, htr135a, htr367a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc356xy, htr135a, htr136b, htr167a, htr367a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd01b, hd68a, htr016a, htr167a, htr467a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              rcases m.htr 5 6 8 (by decide) (by decide) with
                ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
              ·
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, htr026c, htr068a, htr256c, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr067c, htr068b, htr078c])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc012yx, htr016a, htr025a, htr168a, htr256a, htr568a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc357xy, htr013b, htr037b, htr078a, htr135a, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc012yx, hc789yx, htr016a, htr023a, htr167a, htr237a, htr378a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc456yz, htr357c, htr379a, htr467a, htr567c, htr679a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc012yx, hc789zy, htr014a, htr023a, htr148a, htr237a, htr379a, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc012yx, hc468yz, htr018a, htr025a, htr189a, htr256a, htr489a, htr568a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a]
                ·
                  linarith only [hlam, hd46a, hd78b, htr167a, htr168b, htr189a, htr467a, htr789a]
              ·
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc456yz, htr016b, htr068a, htr167a, htr467a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc456yz, htr167a, htr168a, htr467a, htr568a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                rcases m.htr 5 6 9 (by decide) (by decide) with
                  ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
                ·
                  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                    linarith only [hlam, htr026c, htr069a, htr256c, htr569a])
                  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, htr067c, htr069b, htr079c])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, htr068c, htr069b, htr089c])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                    linarith only [hlam, hc357xy, htr013b, htr037b, htr079a, htr135a, htr379a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                    linarith only [hlam, hc358xy, htr013b, htr038b, htr089a, htr135a, htr389a])
                  obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc012yx, hc789xy, htr016a, htr023a, htr167a, htr237a, htr379a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc456yz, htr357c, htr378a, htr467a, htr567c, htr678a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a]
                  ·
                    linarith only [hlam, hd12a, hd78b, htr123a, htr238a, htr389a, htr789a]
                ·
                  rcases m.htr 5 6 10 (by decide) (by decide) with
                    ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                  ·
                    have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                      linarith only [hlam, htr026c, htr0610a, htr256c, htr5610a])
                    obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                    have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                      linarith only [hlam, htr0610b, htr067c, htr0710c])
                    obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, htr0610b, htr068c, htr0810c])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                      linarith only [hlam, hc357xy, htr013b, htr037b, htr0710a, htr135a, htr3710a])
                    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                    have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                      linarith only [hlam, hc358xy, htr013b, htr038b, htr0810a, htr135a, htr3810a])
                    obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc012yx, hc7810xy, htr016a, htr023a, htr167a, htr237a, htr3710a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc456yz, htr357c, htr378a, htr467a, htr567c, htr678a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    rcases m.htr 7 8 10 (by decide) (by decide) with
                      ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    ·
                      linarith only [hlam, hd12a, hd810b, htr123a, htr237a, htr378a, htr7810a]
                    ·
                      linarith only [hlam, hd12a, hd78b, htr123a, htr238a, htr3810a, htr7810a]
                  ·
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc456yz, htr357c, htr378a, htr467a, htr567c, htr678a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                        linarith only [hlam, hc012yx, hc789yx, htr016a, htr023a, htr167a, htr237a, htr378a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc456yz, htr357c, htr379a, htr467a, htr567c, htr679a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc012yx, hc789zy, htr014a, htr023a, htr148a, htr237a, htr379a, htr489a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                        linarith only [hlam, hc012yx, hc478yz, htr018a, htr023a, htr189a, htr237a, htr378a, htr489a])
                      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc358xy, htr135a, htr138b, htr189a, htr389a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a]
                      ·
                        linarith only [hlam, hd12a, hd78b, htr123a, htr238a, htr389a, htr789a]
                    ·
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc012yx, hc789xy, htr016a, htr023a, htr167a, htr237a, htr379a, htr678a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                        linarith only [hlam, hc357xy, htr135a, htr137b, htr179a, htr379a])
                      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hd01b, hd47a, htr016a, htr167a, htr478a, htr678a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hd01b, hd78a, htr017a, htr179a, htr478a, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc012yx, hc789yz, htr014a, htr023a, htr147a, htr238a, htr389a, htr479a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hc456yz, htr358c, htr389a, htr468a, htr568c, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd01b, hd78a, htr016a, htr168a, htr689a, htr789a]
                      ·
                        linarith only [hlam, hd01b, hd89a, htr016a, htr167a, htr678a, htr789a]
            ·
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc012yx, hc678xy, htr014a, htr023a, htr146a, htr236a, htr368a, htr467a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc356xy, htr135a, htr136b, htr168a, htr368a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                linarith only [hlam, hc012yx, hc679xy, htr014a, htr023a, htr146a, htr236a, htr369a, htr467a])
              obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc356xy, htr135a, htr136b, htr169a, htr369a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd01b, hd67a, htr016a, htr168a, htr467a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc012yx, hc678yz, htr014a, htr023a, htr146a, htr237a, htr378a, htr468a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc357xy, htr135a, htr137b, htr178a, htr378a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hd01b, hd67a, htr016a, htr169a, htr467a, htr469a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc012yx, hc689yz, htr014a, htr023a, htr146a, htr238a, htr389a, htr469a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd01b, hd89a, htr014a, htr146a, htr468a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc367zy, htr378c, htr389a, htr678a, htr789a]
              ·
                linarith only [hlam, hd01b, hd68a, htr017a, htr178a, htr689a, htr789a]
        ·
          have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
            linarith only [hlam, hc345yx, htr013b, htr0310a, htr135a, htr2310a, htr234a])
          obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
            linarith only [hlam, htr0310c, htr036b, htr0610b])
          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0310c, htr037b, htr0710b])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr026c, htr0610a, htr236c, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc6710yx, htr023c, htr0310a, htr236a, htr3610b, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc356xy, htr135a, htr136b, htr167a, htr367a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr027c, htr0710a, htr237c, htr3710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, hc346zy, htr2310a, htr236a, htr3610b, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd01b, hd610a, htr016a, htr167a, htr4610a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          rcases m.htr 6 7 10 (by decide) (by decide) with
            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          ·
            linarith only [hlam, hc367zy, htr2310a, htr237a, htr3710b, htr6710a]
          ·
            linarith only [hlam, hd01b, hd710a, htr014a, htr146a, htr467a, htr6710a]
      ·
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, hc345yx, htr013b, htr039a, htr135a, htr234a, htr239a])
        obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, htr036b, htr039c, htr069b])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr037b, htr039c, htr079b])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr026c, htr069a, htr236c, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc679yx, htr023c, htr039a, htr236a, htr367a, htr369b])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc356xy, htr135a, htr136b, htr167a, htr367a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr027c, htr079a, htr237c, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc346zy, htr236a, htr239a, htr369b, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd01b, hd69a, htr016a, htr167a, htr467a, htr469a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc367zy, htr237a, htr239a, htr379b, htr679a]
        ·
          linarith only [hlam, hd01b, hd79a, htr014a, htr146a, htr467a, htr679a]
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc345yx, htr013b, htr038a, htr135a, htr234a, htr238a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr036b, htr038c, htr068b])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr037b, htr038c, htr078b])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr026c, htr068a, htr236c, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc678yx, htr023c, htr038a, htr236a, htr367a, htr368b])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc356xy, htr135a, htr136b, htr167a, htr367a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr027c, htr078a, htr237c, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc346zy, htr236a, htr238a, htr368b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd01b, hd68a, htr016a, htr167a, htr467a, htr468a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hc367zy, htr237a, htr238a, htr378b, htr678a]
      ·
        linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a]
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc345yx, htr013b, htr037a, htr135a, htr234a, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr036b, htr037c, htr067b])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr026c, htr067a, htr236c, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc678xy, htr023c, htr037a, htr236a, htr367b, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hc356xy, htr135a, htr136b, htr168a, htr368a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc346zy, htr236a, htr237a, htr367b, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd01b, hd67a, htr016a, htr168a, htr467a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc012yx, hc678yz, htr014a, htr025a, htr146a, htr257a, htr468a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hc012yx, hc567zy, htr014a, htr027a, htr146a, htr278a, htr467a, htr578a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc347yx, htr234a, htr237c, htr278a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr378a, htr678a]
    ·
      linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a]

theorem shard_405 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr356c : m.d 3 6 < m.d 5 6)
    (htr357c : m.d 3 7 < m.d 5 7)
    (htr358c : m.d 3 8 < m.d 5 8)
    : False :=
  proof_shard_405 m htr013b htr014a htr016a htr016b htr017a htr018a htr023a htr023c htr025a htr026c htr027a htr027c htr036b htr123a htr123c htr125a htr134b htr135a htr136b htr234a htr236a htr236c htr256a htr256c htr257a htr346a htr347a htr348a htr356c htr357c htr358c

#print axioms shard_405
end Jsp404.NoSatElevenDBMTerminal
