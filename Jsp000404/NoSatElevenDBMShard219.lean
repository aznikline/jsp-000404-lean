import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_219 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr258a : m.d 5 8 + lam ≤ m.d 2 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348c : m.d 3 8 < m.d 4 8)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr358c : m.d 3 8 < m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  have hd37a := (m.hrange 3 7 (by decide)).1
  have hd38a := (m.hrange 3 8 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  obtain ⟨hd48a, hd48braw⟩ := m.hrange 4 8 (by decide)
  have hd48b : m.d 4 8 < 4*lam := by
    linarith only [hd48braw, hp]
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
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd13b, hd67a, htr135a, htr235a, htr236a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd13b, hd68a, htr135a, htr235a, htr236a, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hd13b, hd69a, htr135a, htr235a, htr236a, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, hd13b, hd610a, htr135a, htr235a, htr236a, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc034zy, htr047a, htr234a, htr237a, htr347c])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, hc134zy, htr147a, htr234a, htr237a, htr347c])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc136zy, htr167a, htr236a, htr237a, htr367c])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc346yz, htr236a, htr237a, htr367c, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 0 3 5 (by decide) (by decide) with
      ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
    ·
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc345xy, htr035a, htr037a, htr234a, htr237a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc345xy, htr034c, htr035a, htr046a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc345xy, htr034c, htr035a, htr048a, htr348a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc356yx, htr035a, htr036c, htr068a, htr368a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      rcases m.htr 1 4 6 (by decide) (by decide) with
        ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
      ·
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr146a, htr148a, htr348a, htr467a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr378a, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc347xy, htr234a, htr237b, htr278a, htr378a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc012xy, hc567yz, htr014a, htr027a, htr146a, htr278a, htr467a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc012xy, hc678zy, htr014a, htr025a, htr146a, htr257a, htr468a, htr578a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc346yz, htr023b, htr038a, htr236a, htr368c, htr468a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc789xy, htr037a, htr038a, htr378b, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13b, hd89a, htr035a, htr038a, htr135a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd13b, hd78a, htr135a, htr357c, htr379a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc012xy, hc789yz, htr014a, htr025a, htr148a, htr257a, htr489a, htr579a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc026yx, hc478zy, htr025a, htr068a, htr257a, htr489a, htr578a, htr689a]
        ·
          linarith only [hlam, hc346yz, htr368b, htr389a, htr468a, htr689a]
      ·
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr368a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd34a, hd78b, htr146a, htr147a, htr346a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34a, hd47b, htr234a, htr237a, htr378a, htr478a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc347xy, htr234a, htr237b, htr278a, htr378a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd34a, hd79b, htr146a, htr147a, htr346a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd34a, hd47b, htr234a, htr237a, htr379a, htr479a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc347xy, htr234a, htr237b, htr279a, htr379a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc024yx, hc457zy, htr027a, htr046a, htr146a, htr147a, htr278a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc024yx, hc478zy, htr025a, htr046a, htr146a, htr148a, htr257a, htr578a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc134zy, htr023b, htr038a, htr148a, htr234a, htr348c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13b, hd89a, htr035a, htr038a, htr135a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd38a, hd45b, htr145a, htr148a, htr389a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc024yx, hc457zy, htr027a, htr046a, htr146a, htr147a, htr279a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc024yx, hc789yz, htr025a, htr046a, htr257a, htr468a, htr579a, htr689a]
        ·
          linarith only [hlam, hc024yx, hc678zy, htr025a, htr048a, htr257a, htr489a, htr578a, htr689a]
    ·
      rcases m.htr 1 4 6 (by decide) (by decide) with
        ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
      ·
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr146a, htr148a, htr348a, htr467a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr378a, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc013xy, hc567yz, htr014a, htr035a, htr146a, htr357c, htr378a, htr467a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc012xy, hc678zy, htr014a, htr025a, htr146a, htr257a, htr468a, htr578a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc346yz, htr236a, htr238a, htr368c, htr468a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc789xy, htr237a, htr238a, htr378b, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13b, hd89a, htr135a, htr235a, htr238a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc013xy, hc567yz, htr014a, htr035a, htr146a, htr357c, htr379a, htr467a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc012xy, hc789yz, htr014a, htr025a, htr148a, htr257a, htr489a, htr579a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc346yz, htr368a, htr468c, htr489a, htr689a]
        ·
          linarith only [hlam, hc346yz, htr368b, htr389a, htr468a, htr689a]
      ·
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr368a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr167a, htr168a, htr346a, htr468a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr369a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr167a, htr169a, htr346a, htr469a])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd34a, hd78b, htr146a, htr147a, htr346a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34a, hd47b, htr234a, htr237a, htr378a, htr478a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd34a, hd79b, htr146a, htr147a, htr346a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd34a, hd47b, htr234a, htr237a, htr379a, htr479a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hd34a, hd710b, htr146a, htr147a, htr346a, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
          linarith only [hlam, hd34a, hd47b, htr234a, htr237a, htr3710a, htr4710a])
        obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc034yx, hc457zy, htr035a, htr046a, htr146a, htr147a, htr357c, htr378a, htr578a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc457zy, htr047a, htr048a, htr478b, htr578a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd34a, hd89b, htr046a, htr048a, htr346a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd13b, hd79a, htr135a, htr357c, htr378a, htr578a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc457zy, htr047a, htr049a, htr479b, htr579a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd34a, hd910b, htr046a, htr049a, htr346a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc457zy, htr478c, htr489a, htr578a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc457zy, htr479c, htr4910a, htr579a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd13b, hd89a, htr135a, htr357c, htr379a, htr7910a, htr8910a]
          ·
            linarith only [hlam, hd13b, hd910a, htr135a, htr357c, htr378a, htr789a, htr8910a]
        ·
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd13b, hd78a, htr135a, htr357c, htr379a, htr578a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hd13b, hd78a, htr135a, htr357c, htr3710a, htr5710a, htr578a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc012xy, hc789yz, htr016a, htr025a, htr168a, htr257a, htr579a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc012xy, hc7910yz, htr016a, htr025a, htr169a, htr257a, htr5710a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr578a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd12b, hd910a, htr125a, htr257a, htr579a, htr7910a])
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
      linarith only [hlam, hd13b, hd78a, htr135a, htr235a, htr237a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd13b, hd79a, htr135a, htr235a, htr237a, htr379a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
      linarith only [hlam, hd13b, hd710a, htr135a, htr235a, htr237a, htr3710a])
    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
    rcases m.htr 0 3 5 (by decide) (by decide) with
      ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
    ·
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc345xy, htr034c, htr035a, htr046a, htr346a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc356yx, htr035a, htr036c, htr067a, htr367a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      rcases m.htr 2 3 8 (by decide) (by decide) with
        ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
      ·
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc134zy, htr148a, htr234a, htr238a, htr348c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc346yz, htr236a, htr238a, htr368c, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc347yz, htr237a, htr238a, htr378c, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc367yz, htr237a, htr238a, htr378c, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 4 6 7 (by decide) (by decide) with
          ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
        ·
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd34a, hd78b, htr146a, htr147a, htr346a, htr478a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd37a, hd45b, htr145a, htr147a, htr379a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd34a, hd89b, htr146a, htr148a, htr346a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd34a, hd48b, htr234a, htr238a, htr389a, htr489a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
            linarith only [hlam, hc348xy, htr234a, htr238b, htr289a, htr389a])
          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc024yx, hc578yz, htr028a, htr046a, htr289a, htr467a, htr589a, htr678a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hc024yx, hc789zy, htr025a, htr046a, htr258a, htr467a, htr589a, htr679a]
          ·
            linarith only [hlam, hd34a, hd78b, htr347a, htr479a, htr678a, htr679a]
        ·
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr367a, htr467a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd34a, hd68b, htr146a, htr147a, htr347a, htr468a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc346yz, htr367b, htr379a, htr467a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd36a, hd78b, htr367a, htr478a, htr479a, htr679a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc012xy, hc789zy, htr014a, htr025a, htr147a, htr258a, htr479a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
            linarith only [hlam, hc026yx, hc568yz, htr028a, htr067a, htr289a, htr467a, htr468a, htr589a])
          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc348xy, htr234a, htr238b, htr289a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd36a, hd89b, htr367a, htr467a, htr468a, htr678c, htr789a]
          ·
            linarith only [hlam, hd34a, hd78b, htr234a, htr238a, htr389a, htr789a]
      ·
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13b, hd89a, htr135a, htr235a, htr238a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hd13b, hd810a, htr135a, htr235a, htr238a, htr3810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        rcases m.htr 2 3 9 (by decide) (by decide) with
          ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
        ·
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hc346yz, htr236a, htr239a, htr369c, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc347yz, htr237a, htr239a, htr379c, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc367yz, htr237a, htr239a, htr379c, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc378yz, htr238a, htr239a, htr389c, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd34a, hd89b, htr346a, htr467a, htr678a, htr789a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr367a, htr467a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd34a, hd69b, htr146a, htr147a, htr347a, htr469a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hd01a, hd89b, htr014a, htr147a, htr478a, htr789a]
            ·
              linarith only [hlam, hd36a, hd79b, htr367a, htr478a, htr479a, htr678a]
          ·
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hd01a, hd79b, htr014a, htr146a, htr467a, htr679a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd34a, hd79b, htr146a, htr147a, htr346a, htr479a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hd34a, hd79b, htr347a, htr478a, htr678a, htr679a]
            ·
              linarith only [hlam, hd37a, hd45b, htr145a, htr147a, htr378a, htr478a]
        ·
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hd13b, hd910a, htr135a, htr235a, htr239a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 2 3 10 (by decide) (by decide) with
            ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
          ·
            have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
              linarith only [hlam, hc137zy, htr1710a, htr2310a, htr237a, htr3710c])
            obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, hc346yz, htr2310a, htr236a, htr3610c, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hc347yz, htr2310a, htr237a, htr3710c, htr4710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc367yz, htr2310a, htr237a, htr3710c, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc378yz, htr2310a, htr238a, htr3810c, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hc379yz, htr2310a, htr239a, htr3910c, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hd36a, hd710b, htr1710a, htr178a, htr367a, htr678a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hd37a, hd810b, htr178a, htr179a, htr379a, htr7810a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd34a, hd810b, htr346a, htr467a, htr678a, htr7810a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr367a, htr467a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hd34a, hd610b, htr146a, htr147a, htr347a, htr4610a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              rcases m.htr 4 7 9 (by decide) (by decide) with
                ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
              ·
                linarith only [hlam, hd01a, hd910b, htr014a, htr147a, htr479a, htr7910a]
              ·
                linarith only [hlam, hd01a, hd710b, htr017a, htr179a, htr4710a, htr479a]
            ·
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hd01a, hd710b, htr017a, htr178a, htr6710a, htr678a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hd37a, hd910b, htr178a, htr179a, htr378a, htr7910a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hd01a, hd710b, htr014a, htr146a, htr467a, htr6710a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                linarith only [hlam, hd34a, hd710b, htr146a, htr147a, htr346a, htr4710a])
              obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
              rcases m.htr 4 7 9 (by decide) (by decide) with
                ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
              ·
                linarith only [hlam, hd34a, hd710b, htr1710a, htr179a, htr347a, htr479a]
              ·
                linarith only [hlam, hd37a, hd45b, htr145a, htr147a, htr379a, htr479a]
          ·
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hd34a, hd89b, htr346a, htr467a, htr678a, htr789a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                  linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr367a, htr467a])
                obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
                have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                  linarith only [hlam, hc346yz, htr146a, htr147a, htr367a, htr467b])
                obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
                rcases m.htr 4 7 8 (by decide) (by decide) with
                  ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                ·
                  linarith only [hlam, hd01a, hd89b, htr014a, htr147a, htr478a, htr789a]
                ·
                  linarith only [hlam, hc346yz, htr367a, htr467c, htr478a, htr678a]
              ·
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc347yz, htr378b, htr389a, htr478a, htr789a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc378yz, htr389a, htr478a, htr479a, htr789b])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc378yz, htr389a, htr678a, htr679a, htr789b])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  linarith only [hlam, hc378yz, htr389b, htr3910a, htr789a, htr8910a])
                obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc378yz, htr389a, htr479c, htr4910a, htr789c, htr8910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc378yz, htr389a, htr789c, htr7910a, htr8910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                  linarith only [hlam, hd01a, hd910b, htr014a, htr147a, htr479a, htr7910a])
                obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
                have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr149a, htr149b, htr149c, _, _⟩
                  linarith only [hlam, hd34a, hd910b, htr147a, htr149a, htr347a, htr4910a])
                obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hd34a, hd910b, htr346a, htr467a, htr679a, htr7910a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                rcases m.htr 1 4 6 (by decide) (by decide) with
                  ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
                ·
                  linarith only [hlam, hc346yz, htr146a, htr149a, htr367a, htr467b, htr479b]
                ·
                  linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr367a, htr467a]
            ·
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc136zy, htr167a, htr367b, htr378a, htr678a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc367yz, htr167a, htr168a, htr378a, htr678b])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hc367yz, htr378a, htr467a, htr468a, htr678b])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc367yz, htr168c, htr189a, htr378a, htr678c, htr789a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, htr168b, htr169c, htr189b])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hd01a, hd89b, htr014a, htr146a, htr468a, htr689a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hd01a, hd910b, htr016a, htr168a, htr689a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd01a, hd89b, htr016a, htr169a, htr6910a, htr8910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 6 7 9 (by decide) (by decide) with
                ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
              ·
                have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                  linarith only [hlam, hd34a, hd79b, htr146a, htr147a, htr346a, htr467c, htr679a])
                obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
                rcases m.htr 4 7 8 (by decide) (by decide) with
                  ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                ·
                  linarith only [hlam, hd34a, hd79b, htr347a, htr478a, htr678a, htr679a]
                ·
                  linarith only [hlam, hd37a, hd45b, htr145a, htr147a, htr378a, htr478a]
              ·
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc367yz, htr379a, htr679c, htr6910a, htr7910a]
                ·
                  linarith only [hlam, hc367yz, htr379b, htr3910a, htr679a, htr7910a]
    ·
      rcases m.htr 1 4 6 (by decide) (by decide) with
        ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
      ·
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc013xy, hc367yz, htr014a, htr035a, htr146a, htr235a, htr237a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc346yz, htr146a, htr147a, htr367a, htr467b])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc346yz, htr367a, htr467c, htr478a, htr678a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc013xy, hc378yz, htr014a, htr035a, htr147a, htr235a, htr238a, htr478a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc346yz, htr367b, htr379a, htr467a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc346yz, htr367a, htr467c, htr479a, htr679a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc012xy, hc789zy, htr014a, htr025a, htr147a, htr258a, htr479a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc013xy, hc578yz, htr014a, htr035a, htr147a, htr358c, htr389a, htr478a, htr589a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd01a, hd89b, htr014a, htr147a, htr478a, htr789a]
        ·
          linarith only [hlam, hd34a, hd78b, htr234a, htr238a, htr389a, htr789a]
      ·
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr367a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc456yx, htr145a, htr146c, htr167a, htr467a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd36a, hd45b, htr145a, htr146a, htr368a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc456yx, htr145a, htr146c, htr168a, htr468a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd34a, hd78b, htr146a, htr147a, htr346a, htr467c, htr678a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc013xy, hc378yz, htr016a, htr035a, htr167a, htr235a, htr238a, htr678a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc134zy, htr148a, htr234a, htr238a, htr348c])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd37a, hd45b, htr145a, htr147a, htr379a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd34a, hd89b, htr146a, htr148a, htr346a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd34a, hd48b, htr234a, htr238a, htr389a, htr489a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc013xy, hc578yz, htr016a, htr035a, htr167a, htr358c, htr389a, htr589a, htr678a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hc012xy, hc789zy, htr016a, htr025a, htr167a, htr258a, htr589a, htr679a]
          ·
            linarith only [hlam, hd34a, hd78b, htr347a, htr479a, htr678a, htr679a]
        ·
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc013xy, hc367yz, htr017a, htr035a, htr178a, htr235a, htr237a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hc367yz, htr237a, htr238a, htr378c, htr678a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd13b, hd89a, htr135a, htr235a, htr238a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc367yz, htr378a, htr468c, htr489a, htr678c, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hd34a, hd89b, htr146a, htr148a, htr346a, htr489a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr239a, htr239b, htr239c, _, _⟩
            linarith only [hlam, hc013xy, hc389yz, htr016a, htr035a, htr168a, htr235a, htr239a, htr689a])
          obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hc137zy, htr179a, htr237a, htr239a, htr379c])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd34a, hd79b, htr178a, htr179a, htr347a, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 1 4 7 (by decide) (by decide) with
            ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
          ·
            linarith only [hlam, hc347yz, htr147a, htr148a, htr378a, htr478b]
          ·
            linarith only [hlam, hd37a, hd45b, htr145a, htr147a, htr378a, htr478a]

theorem shard_219 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr258a : m.d 5 8 + lam ≤ m.d 2 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348c : m.d 3 8 < m.d 4 8)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr358c : m.d 3 8 < m.d 3 5)
    : False :=
  proof_shard_219 m htr014a htr016a htr017a htr023b htr025a htr027a htr028a htr034c htr036c htr125a htr135a htr145a htr234a htr235a htr236a htr257a htr258a htr346a htr347a htr347c htr348a htr348c htr357c htr358c

#print axioms shard_219
end Jsp404.NoSatElevenDBMTerminal
