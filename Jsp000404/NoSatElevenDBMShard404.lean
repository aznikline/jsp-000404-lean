import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_404 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr258a : m.d 2 5 + lam ≤ m.d 5 8)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr348b : m.d 4 8 < m.d 3 8)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr358b : m.d 3 5 < m.d 3 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  obtain ⟨hd37a, hd37braw⟩ := m.hrange 3 7 (by decide)
  have hd37b : m.d 3 7 < 4*lam := by
    linarith only [hd37braw, hp]
  obtain ⟨hd38a, hd38braw⟩ := m.hrange 3 8 (by decide)
  have hd38b : m.d 3 8 < 4*lam := by
    linarith only [hd38braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd48a := (m.hrange 4 8 (by decide)).1
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
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc026xy, hc026yx, hc026yz, hc026zy⟩ := endpoint_caps m 0 2 6 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc379xy, hc379yx, hc379yz, hc379zy⟩ := endpoint_caps m 3 7 9 (by decide) (by decide)
  obtain ⟨hc389xy, hc389yx, hc389yz, hc389zy⟩ := endpoint_caps m 3 8 9 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd13a, hd67b, htr135a, htr235a, htr236a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd13a, hd68b, htr135a, htr235a, htr236a, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hd13a, hd69b, htr135a, htr235a, htr236a, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, hd13a, hd610b, htr135a, htr235a, htr236a, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr135a, htr235a, htr237a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd13a, hd79b, htr135a, htr235a, htr237a, htr379a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
      linarith only [hlam, hd13a, hd710b, htr135a, htr235a, htr237a, htr3710a])
    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
    rcases m.htr 0 3 5 (by decide) (by decide) with
      ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
    ·
      rcases m.htr 1 4 6 (by decide) (by decide) with
        ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
      ·
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr367a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc456xy, htr145a, htr146b, htr167a, htr467a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr368a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc456xy, htr145a, htr146b, htr168a, htr468a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc013yx, hc367zy, htr017a, htr035a, htr178a, htr235a, htr237a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc367zy, htr237a, htr238a, htr378b, htr678a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd13a, hd89b, htr135a, htr235a, htr238a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc367zy, htr378c, htr389a, htr678a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc367zy, htr378a, htr468b, htr489a, htr678b, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hd34b, hd89a, htr146a, htr148a, htr346a, htr489a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr239a, htr239b, htr239c, _, _⟩
            linarith only [hlam, hc013yx, hc389zy, htr016a, htr035a, htr168a, htr235a, htr239a, htr689a])
          obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hc137yz, htr179a, htr237a, htr239a, htr379b])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd34b, hd79a, htr178a, htr179a, htr347a, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 1 4 7 (by decide) (by decide) with
            ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
          ·
            linarith only [hlam, hd37b, hd45a, htr145a, htr147a, htr378a, htr478a]
          ·
            linarith only [hlam, hc347zy, htr147a, htr148a, htr378a, htr478c]
        ·
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd34b, hd78a, htr146a, htr147a, htr346a, htr467b, htr678a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc013yx, hc378zy, htr016a, htr035a, htr167a, htr235a, htr238a, htr678a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc134yz, htr148a, htr234a, htr238a, htr348b])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd37b, hd45a, htr145a, htr147a, htr379a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd34b, hd89a, htr146a, htr148a, htr346a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd34b, hd48a, htr234a, htr238a, htr389a, htr489a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc013yx, hc578zy, htr016a, htr035a, htr167a, htr358b, htr389a, htr589a, htr678a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd34b, hd78a, htr347a, htr479a, htr678a, htr679a]
          ·
            linarith only [hlam, hc012yx, hc789yz, htr016a, htr025a, htr167a, htr258a, htr589a, htr679a]
      ·
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc013yx, hc367zy, htr014a, htr035a, htr146a, htr235a, htr237a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc346zy, htr146a, htr147a, htr367a, htr467c])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc346zy, htr367c, htr378a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc346zy, htr367a, htr467b, htr478a, htr678a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc013yx, hc378zy, htr014a, htr035a, htr147a, htr235a, htr238a, htr478a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc346zy, htr367c, htr379a, htr467a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc346zy, htr367a, htr467b, htr479a, htr679a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc012yx, hc789yz, htr014a, htr025a, htr147a, htr258a, htr479a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc013yx, hc578zy, htr014a, htr035a, htr147a, htr358b, htr389a, htr478a, htr589a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd34b, hd78a, htr234a, htr238a, htr389a, htr789a]
        ·
          linarith only [hlam, hd01b, hd89a, htr014a, htr147a, htr478a, htr789a]
    ·
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc345yx, htr034b, htr035a, htr046a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc356xy, htr035a, htr036b, htr067a, htr367a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      rcases m.htr 2 3 8 (by decide) (by decide) with
        ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
      ·
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr135a, htr235a, htr238a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hd13a, hd810b, htr135a, htr235a, htr238a, htr3810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        rcases m.htr 2 3 9 (by decide) (by decide) with
          ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
        ·
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hd13a, hd910b, htr135a, htr235a, htr239a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 2 3 10 (by decide) (by decide) with
            ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
          ·
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc136yz, htr167a, htr367c, htr378a, htr678a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc367zy, htr167a, htr168a, htr378a, htr678c])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc346zy, htr367c, htr378a, htr467a, htr678a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hc367zy, htr378a, htr467a, htr468a, htr678c])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc367zy, htr378c, htr389a, htr678a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc367zy, htr168b, htr189a, htr378a, htr678b, htr789a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, htr168c, htr169b, htr189c])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hd01b, hd89a, htr014a, htr146a, htr468a, htr689a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hd01b, hd910a, htr016a, htr168a, htr689a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd01b, hd89a, htr016a, htr169a, htr6910a, htr8910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 6 7 9 (by decide) (by decide) with
                ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
              ·
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc367zy, htr379c, htr3910a, htr679a, htr7910a]
                ·
                  linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a]
              ·
                have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                  linarith only [hlam, hd34b, hd79a, htr146a, htr147a, htr346a, htr467b, htr679a])
                obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
                rcases m.htr 4 7 8 (by decide) (by decide) with
                  ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                ·
                  linarith only [hlam, hd37b, hd45a, htr145a, htr147a, htr378a, htr478a]
                ·
                  linarith only [hlam, hd34b, hd79a, htr347a, htr478a, htr678a, htr679a]
            ·
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc347zy, htr378c, htr389a, htr478a, htr789a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc378zy, htr389a, htr478a, htr479a, htr789c])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc378zy, htr389a, htr678a, htr679a, htr789c])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  linarith only [hlam, hc378zy, htr389c, htr3910a, htr789a, htr8910a])
                obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc378zy, htr389a, htr479b, htr4910a, htr789b, htr8910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc378zy, htr389a, htr789b, htr7910a, htr8910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                  linarith only [hlam, hd01b, hd910a, htr014a, htr147a, htr479a, htr7910a])
                obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
                have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr149a, htr149b, htr149c, _, _⟩
                  linarith only [hlam, hd34b, hd910a, htr147a, htr149a, htr347a, htr4910a])
                obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hd34b, hd910a, htr346a, htr467a, htr679a, htr7910a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                rcases m.htr 1 4 6 (by decide) (by decide) with
                  ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
                ·
                  linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr367a, htr467a]
                ·
                  linarith only [hlam, hc346zy, htr146a, htr149a, htr367a, htr467c, htr479c]
              ·
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hd34b, hd89a, htr346a, htr467a, htr678a, htr789a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                  linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr367a, htr467a])
                obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
                have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                  linarith only [hlam, hc346zy, htr146a, htr147a, htr367a, htr467c])
                obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
                rcases m.htr 4 7 8 (by decide) (by decide) with
                  ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                ·
                  linarith only [hlam, hc346zy, htr367a, htr467b, htr478a, htr678a]
                ·
                  linarith only [hlam, hd01b, hd89a, htr014a, htr147a, htr478a, htr789a]
          ·
            have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
              linarith only [hlam, hc137yz, htr1710a, htr2310a, htr237a, htr3710b])
            obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, hc346zy, htr2310a, htr236a, htr3610b, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hc347zy, htr2310a, htr237a, htr3710b, htr4710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc367zy, htr2310a, htr237a, htr3710b, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc378zy, htr2310a, htr238a, htr3810b, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hc379zy, htr2310a, htr239a, htr3910b, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hd01b, hd710a, htr017a, htr178a, htr6710a, htr678a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hd37b, hd910a, htr178a, htr179a, htr378a, htr7910a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc346zy, htr367c, htr378a, htr467a, htr678a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hd01b, hd710a, htr014a, htr146a, htr467a, htr6710a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hd34b, hd710a, htr146a, htr147a, htr346a, htr4710a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              rcases m.htr 4 7 9 (by decide) (by decide) with
                ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
              ·
                linarith only [hlam, hd37b, hd45a, htr145a, htr147a, htr379a, htr479a]
              ·
                linarith only [hlam, hd34b, hd710a, htr1710a, htr179a, htr347a, htr479a]
            ·
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hd36b, hd710a, htr1710a, htr178a, htr367a, htr678a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hd37b, hd810a, htr178a, htr179a, htr379a, htr7810a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd34b, hd810a, htr346a, htr467a, htr678a, htr7810a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr367a, htr467a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hd34b, hd610a, htr146a, htr147a, htr347a, htr4610a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              rcases m.htr 4 7 9 (by decide) (by decide) with
                ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
              ·
                linarith only [hlam, hd01b, hd710a, htr017a, htr179a, htr4710a, htr479a]
              ·
                linarith only [hlam, hd01b, hd910a, htr014a, htr147a, htr479a, htr7910a]
        ·
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hc346zy, htr236a, htr239a, htr369b, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc347zy, htr237a, htr239a, htr379b, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc367zy, htr237a, htr239a, htr379b, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc378zy, htr238a, htr239a, htr389b, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc346zy, htr367c, htr378a, htr467a, htr678a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hd01b, hd79a, htr014a, htr146a, htr467a, htr679a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd34b, hd79a, htr146a, htr147a, htr346a, htr479a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hd37b, hd45a, htr145a, htr147a, htr378a, htr478a]
            ·
              linarith only [hlam, hd34b, hd79a, htr347a, htr478a, htr678a, htr679a]
          ·
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd34b, hd89a, htr346a, htr467a, htr678a, htr789a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr367a, htr467a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd34b, hd69a, htr146a, htr147a, htr347a, htr469a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hd36b, hd79a, htr367a, htr478a, htr479a, htr678a]
            ·
              linarith only [hlam, hd01b, hd89a, htr014a, htr147a, htr478a, htr789a]
      ·
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc134yz, htr148a, htr234a, htr238a, htr348b])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc346zy, htr236a, htr238a, htr368b, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc347zy, htr237a, htr238a, htr378b, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc367zy, htr237a, htr238a, htr378b, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 4 6 7 (by decide) (by decide) with
          ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
        ·
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr367a, htr467a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd34b, hd68a, htr146a, htr147a, htr347a, htr468a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc346zy, htr367c, htr379a, htr467a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd36b, hd78a, htr367a, htr478a, htr479a, htr679a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc012yx, hc789yz, htr014a, htr025a, htr147a, htr258a, htr479a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
            linarith only [hlam, hc026xy, hc568zy, htr028a, htr067a, htr289a, htr467a, htr468a, htr589a])
          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc348yx, htr234a, htr238c, htr289a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd34b, hd78a, htr234a, htr238a, htr389a, htr789a]
          ·
            linarith only [hlam, hd36b, hd89a, htr367a, htr467a, htr468a, htr678b, htr789a]
        ·
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd34b, hd78a, htr146a, htr147a, htr346a, htr478a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd37b, hd45a, htr145a, htr147a, htr379a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd34b, hd89a, htr146a, htr148a, htr346a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd34b, hd48a, htr234a, htr238a, htr389a, htr489a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
            linarith only [hlam, hc348yx, htr234a, htr238c, htr289a, htr389a])
          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc024xy, hc578zy, htr028a, htr046a, htr289a, htr467a, htr589a, htr678a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd34b, hd78a, htr347a, htr479a, htr678a, htr679a]
          ·
            linarith only [hlam, hc024xy, hc789yz, htr025a, htr046a, htr258a, htr467a, htr589a, htr679a]
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc034yz, htr047a, htr234a, htr237a, htr347b])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc134yz, htr147a, htr234a, htr237a, htr347b])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc136yz, htr167a, htr236a, htr237a, htr367b])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc346zy, htr236a, htr237a, htr367b, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 0 3 5 (by decide) (by decide) with
      ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
    ·
      rcases m.htr 1 4 6 (by decide) (by decide) with
        ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
      ·
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr368a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hd34b, hd67a, htr167a, htr168a, htr346a, htr468a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr369a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, hd34b, hd67a, htr167a, htr169a, htr346a, htr469a])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd34b, hd78a, htr146a, htr147a, htr346a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34b, hd47a, htr234a, htr237a, htr378a, htr478a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd34b, hd79a, htr146a, htr147a, htr346a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd34b, hd47a, htr234a, htr237a, htr379a, htr479a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hd34b, hd710a, htr146a, htr147a, htr346a, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
          linarith only [hlam, hd34b, hd47a, htr234a, htr237a, htr3710a, htr4710a])
        obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd13a, hd78b, htr135a, htr357b, htr379a, htr578a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hd13a, hd78b, htr135a, htr357b, htr3710a, htr5710a, htr578a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc012yx, hc789zy, htr016a, htr025a, htr168a, htr257a, htr579a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc012yx, hc7910zy, htr016a, htr025a, htr169a, htr257a, htr5710a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd12a, hd89b, htr125a, htr257a, htr578a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd12a, hd910b, htr125a, htr257a, htr579a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
          ·
            linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
        ·
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc034xy, hc457yz, htr035a, htr046a, htr146a, htr147a, htr357b, htr378a, htr578a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc457yz, htr047a, htr048a, htr478c, htr578a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd34b, hd89a, htr046a, htr048a, htr346a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd13a, hd79b, htr135a, htr357b, htr378a, htr578a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc457yz, htr047a, htr049a, htr479c, htr579a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd34b, hd910a, htr046a, htr049a, htr346a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc457yz, htr478b, htr489a, htr578a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc457yz, htr479b, htr4910a, htr579a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd13a, hd910b, htr135a, htr357b, htr378a, htr789a, htr8910a]
          ·
            linarith only [hlam, hd13a, hd89b, htr135a, htr357b, htr379a, htr7910a, htr8910a]
      ·
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hd34b, hd67a, htr146a, htr148a, htr348a, htr467a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr378a, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc013yx, hc567zy, htr014a, htr035a, htr146a, htr357b, htr378a, htr467a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc012yx, hc678yz, htr014a, htr025a, htr146a, htr257a, htr468a, htr578a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc346zy, htr236a, htr238a, htr368b, htr468a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc789yx, htr237a, htr238a, htr378c, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr135a, htr235a, htr238a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc013yx, hc567zy, htr014a, htr035a, htr146a, htr357b, htr379a, htr467a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc012yx, hc789zy, htr014a, htr025a, htr148a, htr257a, htr489a, htr579a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc346zy, htr368c, htr389a, htr468a, htr689a]
        ·
          linarith only [hlam, hc346zy, htr368a, htr468b, htr489a, htr689a]
    ·
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc345yx, htr035a, htr037a, htr234a, htr237a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc345yx, htr034b, htr035a, htr046a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc345yx, htr034b, htr035a, htr048a, htr348a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc356xy, htr035a, htr036b, htr068a, htr368a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      rcases m.htr 1 4 6 (by decide) (by decide) with
        ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
      ·
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd36b, hd45a, htr145a, htr146a, htr368a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd34b, hd78a, htr146a, htr147a, htr346a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34b, hd47a, htr234a, htr237a, htr378a, htr478a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc347yx, htr234a, htr237c, htr278a, htr378a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd34b, hd79a, htr146a, htr147a, htr346a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd34b, hd47a, htr234a, htr237a, htr379a, htr479a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc347yx, htr234a, htr237c, htr279a, htr379a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc024xy, hc457yz, htr027a, htr046a, htr146a, htr147a, htr278a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc024xy, hc478yz, htr025a, htr046a, htr146a, htr148a, htr257a, htr578a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc134yz, htr023c, htr038a, htr148a, htr234a, htr348b])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr035a, htr038a, htr135a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd38b, hd45a, htr145a, htr148a, htr389a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc024xy, hc457yz, htr027a, htr046a, htr146a, htr147a, htr279a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc024xy, hc678yz, htr025a, htr048a, htr257a, htr489a, htr578a, htr689a]
        ·
          linarith only [hlam, hc024xy, hc789zy, htr025a, htr046a, htr257a, htr468a, htr579a, htr689a]
      ·
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hd34b, hd67a, htr146a, htr148a, htr348a, htr467a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr378a, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc347yx, htr234a, htr237c, htr278a, htr378a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc012yx, hc567zy, htr014a, htr027a, htr146a, htr278a, htr467a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc012yx, hc678yz, htr014a, htr025a, htr146a, htr257a, htr468a, htr578a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc346zy, htr023c, htr038a, htr236a, htr368b, htr468a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc789yx, htr037a, htr038a, htr378c, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr035a, htr038a, htr135a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd13a, hd78b, htr135a, htr357b, htr379a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc012yx, hc789zy, htr014a, htr025a, htr148a, htr257a, htr489a, htr579a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc346zy, htr368c, htr389a, htr468a, htr689a]
        ·
          linarith only [hlam, hc026xy, hc478yz, htr025a, htr068a, htr257a, htr489a, htr578a, htr689a]

theorem shard_404 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr258a : m.d 2 5 + lam ≤ m.d 5 8)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr348b : m.d 4 8 < m.d 3 8)
    (htr357b : m.d 3 5 < m.d 3 7)
    (htr358b : m.d 3 5 < m.d 3 8)
    : False :=
  proof_shard_404 m htr014a htr016a htr017a htr023c htr025a htr027a htr028a htr034b htr036b htr125a htr135a htr145a htr234a htr235a htr236a htr257a htr258a htr346a htr347a htr347b htr348a htr348b htr357b htr358b

#print axioms shard_404
end Jsp404.NoSatElevenDBMTerminal
