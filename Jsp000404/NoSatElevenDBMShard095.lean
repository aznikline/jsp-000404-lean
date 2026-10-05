import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_095 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047a : m.d 4 7 + lam ≤ m.d 0 4)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr048a : m.d 4 8 + lam ≤ m.d 0 4)
    (htr048c : m.d 0 8 < m.d 0 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
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
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, htr023c, htr036a, htr236a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr035c, htr036b, htr056c])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hc345yx, htr134a, htr136a, htr235a, htr236a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc345yx, htr035b, htr056a, htr134a, htr135c, htr156a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr035b, htr056a, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc567yx, htr023c, htr035a, htr236a, htr356c, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hc345yx, htr025c, htr057a, htr234a, htr235c, htr357a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, htr025b, htr027c, htr057b])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc345yx, htr134a, htr135c, htr157a, htr357a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc568yx, htr023c, htr035a, htr236a, htr356c, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr023c, htr037a, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    rcases m.htr 2 3 8 (by decide) (by decide) with
      ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr023c, htr038a, htr238a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
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
              linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd02a, hd67b, htr023a, htr237a, htr378a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc357xy, htr035a, htr037b, htr078a, htr378a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc012yz, hc467yz, htr024c, htr025a, htr047c, htr078a, htr124a, htr125b, htr156a, htr478a, htr567a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hc012yz, hc678zy, htr023a, htr024c, htr047a, htr124a, htr236a, htr368a, htr478a])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc012yz, hc789xy, htr023a, htr024c, htr047a, htr124a, htr237a, htr379a, htr478a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, hc357xy, htr035a, htr037b, htr079a, htr379a])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc012yz, hc467yz, htr024c, htr025a, htr047c, htr079a, htr124a, htr125b, htr156a, htr479a, htr567a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hc012yz, hc789yz, htr023a, htr024c, htr047a, htr124a, htr238a, htr389a, htr479a])
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
              linarith only [hlam, hd12b, hd89a, htr024c, htr047a, htr124a, htr478a, htr789a]
          ·
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hd02a, hd56b, htr023a, htr236a, htr367a, htr567a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc356xy, htr035a, htr036b, htr067a, htr367a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd12b, hd68a, htr024c, htr046c, htr067a, htr124a, htr467a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              rcases m.htr 5 6 8 (by decide) (by decide) with
                ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
              ·
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, htr056c, htr068a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr067c, htr068b, htr078c])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc357xy, htr035a, htr037b, htr078a, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc012yz, hc789yx, htr023a, htr024c, htr046c, htr067a, htr124a, htr237a, htr378a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc456yz, htr357c, htr379a, htr467a, htr567c, htr679a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc012yz, hc789zy, htr023a, htr024c, htr048a, htr124a, htr237a, htr379a, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, hc012yz, hc468yz, htr024c, htr025a, htr048c, htr089a, htr124a, htr125b, htr156a, htr489a, htr568a])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd02a, hd89b, htr023a, htr237a, htr378a, htr789a]
                ·
                  linarith only [hlam, hd46a, hd78b, htr067a, htr068b, htr089a, htr467a, htr789a]
              ·
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc456yz, htr067a, htr068a, htr467a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                rcases m.htr 5 6 9 (by decide) (by decide) with
                  ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
                ·
                  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                    linarith only [hlam, htr056c, htr069a, htr569a])
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
                    linarith only [hlam, hc357xy, htr035a, htr037b, htr079a, htr379a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                    linarith only [hlam, hc358xy, htr035a, htr038b, htr089a, htr389a])
                  obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc012yz, hc789xy, htr023a, htr024c, htr046c, htr067a, htr124a, htr237a, htr379a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc456yz, htr357c, htr378a, htr467a, htr567c, htr678a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd02a, hd89b, htr023a, htr237a, htr378a, htr789a]
                  ·
                    linarith only [hlam, hd02a, hd78b, htr023a, htr238a, htr389a, htr789a]
                ·
                  rcases m.htr 5 6 10 (by decide) (by decide) with
                    ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                  ·
                    have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                      linarith only [hlam, htr056c, htr0610a, htr5610a])
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
                      linarith only [hlam, hc357xy, htr035a, htr037b, htr0710a, htr3710a])
                    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                    have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                      linarith only [hlam, hc358xy, htr035a, htr038b, htr0810a, htr3810a])
                    obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc012yz, hc7810xy, htr023a, htr024c, htr046c, htr067a, htr124a, htr237a, htr3710a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc456yz, htr357c, htr378a, htr467a, htr567c, htr678a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    rcases m.htr 7 8 10 (by decide) (by decide) with
                      ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    ·
                      linarith only [hlam, hd02a, hd810b, htr023a, htr237a, htr378a, htr7810a]
                    ·
                      linarith only [hlam, hd02a, hd78b, htr023a, htr238a, htr3810a, htr7810a]
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
                        linarith only [hlam, hc012yz, hc789yx, htr023a, htr024c, htr046c, htr067a, htr124a, htr237a, htr378a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc456yz, htr357c, htr379a, htr467a, htr567c, htr679a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc012yz, hc789zy, htr023a, htr024c, htr048a, htr124a, htr237a, htr379a, htr489a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, hc012yz, hc478yz, htr023a, htr024c, htr048c, htr089a, htr124a, htr237a, htr378a, htr489a])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc358xy, htr035a, htr038b, htr089a, htr389a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd02a, hd89b, htr023a, htr237a, htr378a, htr789a]
                      ·
                        linarith only [hlam, hd02a, hd78b, htr023a, htr238a, htr389a, htr789a]
                    ·
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc012yz, hc789xy, htr023a, htr024c, htr046c, htr067a, htr124a, htr237a, htr379a, htr678a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, hc357xy, htr035a, htr037b, htr079a, htr379a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hd12b, hd47a, htr024c, htr046c, htr067a, htr124a, htr478a, htr678a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hd12b, hd78a, htr024c, htr047c, htr079a, htr124a, htr478a, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc012yz, hc789yz, htr023a, htr024c, htr047a, htr124a, htr238a, htr389a, htr479a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hc456yz, htr358c, htr389a, htr468a, htr568c, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd12b, hd78a, htr024c, htr046c, htr068a, htr124a, htr689a, htr789a]
                      ·
                        linarith only [hlam, hd12b, hd89a, htr024c, htr046c, htr067a, htr124a, htr678a, htr789a]
            ·
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc012yz, hc678xy, htr023a, htr024c, htr046a, htr124a, htr236a, htr368a, htr467a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc356xy, htr035a, htr036b, htr068a, htr368a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                linarith only [hlam, hc012yz, hc679xy, htr023a, htr024c, htr046a, htr124a, htr236a, htr369a, htr467a])
              obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc356xy, htr035a, htr036b, htr069a, htr369a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd12b, hd67a, htr024c, htr046c, htr068a, htr124a, htr467a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc012yz, hc678yz, htr023a, htr024c, htr046a, htr124a, htr237a, htr378a, htr468a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc357xy, htr035a, htr037b, htr078a, htr378a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hd12b, hd67a, htr024c, htr046c, htr069a, htr124a, htr467a, htr469a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc012yz, hc689yz, htr023a, htr024c, htr046a, htr124a, htr238a, htr389a, htr469a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd12b, hd78a, htr024c, htr046a, htr124a, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd12b, hd89a, htr024c, htr046a, htr124a, htr468a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc367zy, htr378c, htr389a, htr678a, htr789a]
              ·
                linarith only [hlam, hd12b, hd68a, htr024c, htr047c, htr078a, htr124a, htr689a, htr789a]
        ·
          have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
            linarith only [hlam, hc345yx, htr0310a, htr035a, htr2310a, htr234a])
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
            linarith only [hlam, hc012yz, htr023a, htr024c, htr046c, htr0610a, htr124a, htr236a, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc6710yx, htr123b, htr136a, htr2310a, htr3610b, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc356xy, htr035a, htr036b, htr067a, htr367a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, hc012yz, htr023a, htr024c, htr047c, htr0710a, htr124a, htr237a, htr3710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, hc346zy, htr2310a, htr236a, htr3610b, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd12b, hd610a, htr024c, htr046c, htr067a, htr124a, htr4610a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          rcases m.htr 6 7 10 (by decide) (by decide) with
            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          ·
            linarith only [hlam, hc367zy, htr2310a, htr237a, htr3710b, htr6710a]
          ·
            linarith only [hlam, hd12b, hd710a, htr024c, htr046a, htr124a, htr467a, htr6710a]
      ·
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, hc345yx, htr035a, htr039a, htr234a, htr239a])
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
          linarith only [hlam, hc012yz, htr023a, htr024c, htr046c, htr069a, htr124a, htr236a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc679yx, htr123b, htr136a, htr239a, htr367a, htr369b])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc356xy, htr035a, htr036b, htr067a, htr367a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc012yz, htr023a, htr024c, htr047c, htr079a, htr124a, htr237a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc346zy, htr236a, htr239a, htr369b, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd12b, hd69a, htr024c, htr046c, htr067a, htr124a, htr467a, htr469a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc367zy, htr237a, htr239a, htr379b, htr679a]
        ·
          linarith only [hlam, hd12b, hd79a, htr024c, htr046a, htr124a, htr467a, htr679a]
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc345yx, htr035a, htr038a, htr234a, htr238a])
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
        linarith only [hlam, hc012yz, htr023a, htr024c, htr046c, htr068a, htr124a, htr236a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc678yx, htr123b, htr136a, htr238a, htr367a, htr368b])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc356xy, htr035a, htr036b, htr067a, htr367a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc012yz, htr023a, htr024c, htr047c, htr078a, htr124a, htr237a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc346zy, htr236a, htr238a, htr368b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr024c, htr046c, htr067a, htr124a, htr467a, htr468a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hc367zy, htr237a, htr238a, htr378b, htr678a]
      ·
        linarith only [hlam, hd12b, hd78a, htr024c, htr046a, htr124a, htr467a, htr678a]
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc345yx, htr035a, htr037a, htr234a, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr036b, htr037c, htr067b])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr123b, htr137a, htr237a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc012yz, htr023a, htr024c, htr046c, htr067a, htr124a, htr236a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc678xy, htr123b, htr136a, htr237a, htr367b, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc356xy, htr035a, htr036b, htr068a, htr368a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc346zy, htr236a, htr237a, htr367b, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr024c, htr046c, htr068a, htr124a, htr467a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc012yz, hc678yz, htr024c, htr025a, htr046a, htr124a, htr125b, htr157a, htr468a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc012yz, hc567zy, htr024c, htr027a, htr046a, htr124a, htr127b, htr178a, htr467a, htr578a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc347yx, htr134a, htr137c, htr178a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a]
    ·
      linarith only [hlam, hd12b, hd78a, htr024c, htr046a, htr124a, htr467a, htr678a]

theorem shard_095 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047a : m.d 4 7 + lam ≤ m.d 0 4)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr048a : m.d 4 8 + lam ≤ m.d 0 4)
    (htr048c : m.d 0 8 < m.d 0 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    : False :=
  proof_shard_095 m htr015a htr023a htr023c htr024c htr025a htr025b htr025c htr035a htr035b htr035c htr046a htr046c htr047a htr047c htr048a htr048c htr123a htr123b htr124a htr125b htr127b htr134a htr135c htr234a htr235a htr235c htr236a

#print axioms shard_095
end Jsp404.NoSatElevenDBMTerminal
