import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_152 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr028b : m.d 2 8 < m.d 0 8)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
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
    linarith only [hlam, hc345yx, htr013c, htr036a, htr134a, htr235a, htr236a])
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
    linarith only [hlam, hc345yx, htr025b, htr056a, htr134a, htr135c, htr156a, htr235b])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr025b, htr056a, htr235b, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc567yx, htr023b, htr036a, htr235a, htr356c, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc345yx, htr134a, htr135c, htr157a, htr357a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc568yx, htr023b, htr036a, htr235a, htr356c, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc345yx, htr013c, htr037a, htr134a, htr235a, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, hc345yx, htr134a, htr137a, htr235a, htr237a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    rcases m.htr 2 3 8 (by decide) (by decide) with
      ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
    ·
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc345yx, htr134a, htr138a, htr235a, htr238a])
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
              linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd35a, hd67b, htr235a, htr237a, htr378a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc357xy, htr235a, htr237b, htr278a, htr378a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc012xy, hc467yz, htr015a, htr027a, htr156a, htr278a, htr478a, htr567a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hc012xy, hc678zy, htr013a, htr024a, htr136a, htr247a, htr368a, htr478a])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc012xy, hc789xy, htr013a, htr024a, htr137a, htr247a, htr379a, htr478a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, hc357xy, htr235a, htr237b, htr279a, htr379a])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc012xy, hc467yz, htr015a, htr027a, htr156a, htr279a, htr479a, htr567a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hc012xy, hc789yz, htr013a, htr024a, htr138a, htr247a, htr389a, htr479a])
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
              linarith only [hlam, hd12b, hd89a, htr124a, htr247a, htr478a, htr789a]
          ·
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hd35a, hd56b, htr235a, htr236a, htr367a, htr567a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc356xy, htr026b, htr067a, htr235a, htr236b, htr367a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc356xy, htr235a, htr236b, htr267a, htr367a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd12b, hd68a, htr126a, htr267a, htr467a, htr468a])
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
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, htr026b, htr056c, htr268a, htr568a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc357xy, htr027b, htr078a, htr235a, htr237b, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc012xy, hc789yx, htr013a, htr026a, htr137a, htr267a, htr378a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc456yz, htr357c, htr379a, htr467a, htr567c, htr679a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc012xy, hc789zy, htr013a, htr024a, htr137a, htr248a, htr379a, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hc012xy, hc468yz, htr015a, htr028a, htr156a, htr289a, htr489a, htr568a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd35a, hd89b, htr235a, htr237a, htr378a, htr789a]
                ·
                  linarith only [hlam, hd46a, hd78b, htr267a, htr268b, htr289a, htr467a, htr789a]
              ·
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc456yz, htr026b, htr068a, htr267a, htr467a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hc456yz, htr267a, htr268a, htr467a, htr568a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
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
                    linarith only [hlam, hc357xy, htr027b, htr079a, htr235a, htr237b, htr379a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                    linarith only [hlam, hc358xy, htr028b, htr089a, htr235a, htr238b, htr389a])
                  obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc012xy, hc789xy, htr013a, htr026a, htr137a, htr267a, htr379a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc456yz, htr357c, htr378a, htr467a, htr567c, htr678a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd35a, hd89b, htr235a, htr237a, htr378a, htr789a]
                  ·
                    linarith only [hlam, hd35a, hd78b, htr235a, htr238a, htr389a, htr789a]
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
                      linarith only [hlam, hc357xy, htr027b, htr0710a, htr235a, htr237b, htr3710a])
                    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                    have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                      linarith only [hlam, hc358xy, htr028b, htr0810a, htr235a, htr238b, htr3810a])
                    obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc012xy, hc7810xy, htr013a, htr026a, htr137a, htr267a, htr3710a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc456yz, htr357c, htr378a, htr467a, htr567c, htr678a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    rcases m.htr 7 8 10 (by decide) (by decide) with
                      ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    ·
                      linarith only [hlam, hd35a, hd810b, htr235a, htr237a, htr378a, htr7810a]
                    ·
                      linarith only [hlam, hd35a, hd78b, htr235a, htr238a, htr3810a, htr7810a]
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
                        linarith only [hlam, hc012xy, hc789yx, htr013a, htr026a, htr137a, htr267a, htr378a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc456yz, htr357c, htr379a, htr467a, htr567c, htr679a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc012xy, hc789zy, htr013a, htr024a, htr137a, htr248a, htr379a, htr489a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                        linarith only [hlam, hc012xy, hc478yz, htr013a, htr028a, htr137a, htr289a, htr378a, htr489a])
                      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc358xy, htr235a, htr238b, htr289a, htr389a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd35a, hd89b, htr235a, htr237a, htr378a, htr789a]
                      ·
                        linarith only [hlam, hd35a, hd78b, htr235a, htr238a, htr389a, htr789a]
                    ·
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc012xy, hc789xy, htr013a, htr026a, htr137a, htr267a, htr379a, htr678a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, hc357xy, htr235a, htr237b, htr279a, htr379a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hd12b, hd47a, htr126a, htr267a, htr478a, htr678a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hd12b, hd78a, htr127a, htr279a, htr478a, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc012xy, hc789yz, htr013a, htr024a, htr138a, htr247a, htr389a, htr479a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hc456yz, htr358c, htr389a, htr468a, htr568c, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd12b, hd78a, htr126a, htr268a, htr689a, htr789a]
                      ·
                        linarith only [hlam, hd12b, hd89a, htr126a, htr267a, htr678a, htr789a]
            ·
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc012xy, hc678xy, htr013a, htr024a, htr136a, htr246a, htr368a, htr467a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc356xy, htr235a, htr236b, htr268a, htr368a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                linarith only [hlam, hc012xy, hc679xy, htr013a, htr024a, htr136a, htr246a, htr369a, htr467a])
              obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hc356xy, htr235a, htr236b, htr269a, htr369a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd12b, hd67a, htr126a, htr268a, htr467a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc012xy, hc678yz, htr013a, htr024a, htr137a, htr246a, htr378a, htr468a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc357xy, htr235a, htr237b, htr278a, htr378a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hd12b, hd67a, htr126a, htr269a, htr467a, htr469a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc012xy, hc689yz, htr013a, htr024a, htr138a, htr246a, htr389a, htr469a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd12b, hd78a, htr124a, htr246a, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd12b, hd89a, htr124a, htr246a, htr468a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc367zy, htr378c, htr389a, htr678a, htr789a]
              ·
                linarith only [hlam, hd12b, hd68a, htr127a, htr278a, htr689a, htr789a]
        ·
          have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
            linarith only [hlam, htr023b, htr0310a, htr2310a])
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
            linarith only [hlam, htr036c, htr0610a, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc6710yx, htr023b, htr036a, htr2310a, htr3610b, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc356xy, htr235a, htr236b, htr267a, htr367a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr037c, htr0710a, htr3710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, hc346zy, htr2310a, htr236a, htr3610b, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd12b, hd610a, htr126a, htr267a, htr4610a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          rcases m.htr 6 7 10 (by decide) (by decide) with
            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          ·
            linarith only [hlam, hc367zy, htr2310a, htr237a, htr3710b, htr6710a]
          ·
            linarith only [hlam, hd12b, hd710a, htr124a, htr246a, htr467a, htr6710a]
      ·
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, htr023b, htr039a, htr239a])
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
          linarith only [hlam, htr036c, htr069a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc679yx, htr023b, htr036a, htr239a, htr367a, htr369b])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc356xy, htr235a, htr236b, htr267a, htr367a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr037c, htr079a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc346zy, htr236a, htr239a, htr369b, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd12b, hd69a, htr126a, htr267a, htr467a, htr469a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc367zy, htr237a, htr239a, htr379b, htr679a]
        ·
          linarith only [hlam, hd12b, hd79a, htr124a, htr246a, htr467a, htr679a]
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr023b, htr038a, htr238a])
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
        linarith only [hlam, htr036c, htr068a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc678yx, htr023b, htr036a, htr238a, htr367a, htr368b])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc356xy, htr235a, htr236b, htr267a, htr367a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr037c, htr078a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc346zy, htr236a, htr238a, htr368b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr126a, htr267a, htr467a, htr468a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hc367zy, htr237a, htr238a, htr378b, htr678a]
      ·
        linarith only [hlam, hd12b, hd78a, htr124a, htr246a, htr467a, htr678a]
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr023b, htr037a, htr237a])
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
      linarith only [hlam, htr036c, htr067a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc678xy, htr023b, htr036a, htr237a, htr367b, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc356xy, htr235a, htr236b, htr268a, htr368a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc346zy, htr236a, htr237a, htr367b, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr126a, htr268a, htr467a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc012xy, hc678yz, htr015a, htr024a, htr157a, htr246a, htr468a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc012xy, hc567zy, htr017a, htr024a, htr178a, htr246a, htr467a, htr578a])
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
      linarith only [hlam, hd12b, hd78a, htr124a, htr246a, htr467a, htr678a]

theorem shard_152 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr028b : m.d 2 8 < m.d 0 8)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    : False :=
  proof_shard_152 m htr013a htr013c htr015a htr017a htr023b htr024a htr025b htr026a htr026b htr027a htr027b htr028a htr028b htr035c htr123a htr123b htr124a htr126a htr127a htr134a htr135c htr235a htr235b htr236a htr236b htr246a htr247a htr248a

#print axioms shard_152
end Jsp404.NoSatElevenDBMTerminal
