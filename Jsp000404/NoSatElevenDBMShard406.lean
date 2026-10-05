import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_406 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237b : m.d 2 3 < m.d 2 7)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr348b : m.d 4 8 < m.d 3 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd37a, hd37braw⟩ := m.hrange 3 7 (by decide)
  have hd37b : m.d 3 7 < 4*lam := by
    linarith only [hd37braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
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
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc028xy, hc028yx, hc028yz, hc028zy⟩ := endpoint_caps m 0 2 8 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, htr023c, htr037a, htr237a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, htr235c, htr237b, htr257c])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, htr236c, htr237b, htr267c])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, htr235b, htr257a, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc567xy, htr235a, htr237a, htr356a, htr357c])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc345yx, htr234a, htr235c, htr256a, htr356a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, htr236b, htr267a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hc678yx, htr236a, htr237a, htr367c, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hc679yx, htr236a, htr237a, htr367c, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, hc6710yx, htr236a, htr237a, htr3610a, htr367c])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, hd13a, hd78b, htr135a, htr235a, htr237a, htr378a])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
    linarith only [hlam, hd13a, hd79b, htr135a, htr235a, htr237a, htr379a])
  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hc356yz, htr236a, htr237a, htr367c, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd13a, hd67b, htr136a, htr368a, htr567a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hd13a, hd67b, htr136a, htr369a, htr567a, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hd13a, hd67b, htr136a, htr3610a, htr5610a, htr567a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, htr367c, htr378a, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
    linarith only [hlam, hd13a, hd89b, htr135a, htr356a, htr568a, htr689a])
  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
    linarith only [hlam, hd13a, hd810b, htr135a, htr356a, htr568a, htr6810a])
  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
    linarith only [hlam, hd13a, hd910b, htr135a, htr356a, htr569a, htr6910a])
  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
  rcases m.htr 0 3 5 (by decide) (by decide) with
    ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
  ·
    rcases m.htr 2 3 8 (by decide) (by decide) with
      ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
    ·
      rcases m.htr 1 4 7 (by decide) (by decide) with
        ⟨htr147a, htr147b, htr147c, _, _⟩ | ⟨htr147a, htr147b, htr147c, _, _⟩
      ·
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd37b, hd45a, htr145a, htr147a, htr378a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc457xy, htr145a, htr147b, htr178a, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd37b, hd45a, htr145a, htr147a, htr379a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc457xy, htr145a, htr147b, htr179a, htr479a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc012yx, hc689zy, htr017a, htr025a, htr178a, htr256a, htr569a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc012yx, hc6910zy, htr017a, htr025a, htr179a, htr256a, htr5610a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
      ·
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc012yx, hc678zy, htr014a, htr025a, htr147a, htr256a, htr478a, htr568a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc347zy, htr147a, htr148a, htr378a, htr478c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc012yx, hc689zy, htr014a, htr025a, htr148a, htr256a, htr489a, htr569a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a]
        ·
          linarith only [hlam, hc347zy, htr378a, htr478b, htr489a, htr789a]
    ·
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc034yz, htr048a, htr234a, htr238a, htr348b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc134yz, htr148a, htr234a, htr238a, htr348b])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc347zy, htr237a, htr238a, htr378b, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc012yx, hc678zy, htr014a, htr025a, htr147a, htr256a, htr478a, htr568a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc024xy, hc468yz, htr025a, htr047a, htr147a, htr148a, htr256a, htr568a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc012yx, hc689zy, htr014a, htr025a, htr148a, htr256a, htr489a, htr569a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr049a, htr049b, htr049c, _, _⟩
        linarith only [hlam, hc468yz, htr048a, htr049a, htr489c, htr689a])
      obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd34b, hd910a, htr047a, htr049a, htr347a, htr4910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc468yz, htr489a, htr689c, htr6910a, htr8910a]
      ·
        linarith only [hlam, hc468yz, htr489b, htr4910a, htr689a, htr8910a]
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc345yx, htr034b, htr035a, htr047a, htr347a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc345yx, htr034b, htr035a, htr048a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc357xy, htr035a, htr037b, htr078a, htr378a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc012yx, hc678zy, htr014a, htr025a, htr147a, htr256a, htr478a, htr568a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc024xy, hc468yz, htr025a, htr047a, htr147a, htr148a, htr256a, htr568a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      rcases m.htr 4 8 9 (by decide) (by decide) with
        ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
      ·
        linarith only [hlam, hd45a, hd68b, htr145a, htr148a, htr489a, htr689a]
      ·
        linarith only [hlam, hc024xy, hc678zy, htr025a, htr048a, htr256a, htr489a, htr568a, htr789a]
    ·
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc012yx, hc689zy, htr017a, htr025a, htr178a, htr256a, htr569a, htr789a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
        linarith only [hlam, hc167yz, htr078b, htr0810a, htr178a, htr678c, htr6810a])
      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc027xy, hc168yz, htr025a, htr078a, htr189a, htr256a, htr568a, htr789a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hc028xy, hc689zy, htr025a, htr0810a, htr1810a, htr189a, htr256a, htr569a])
      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc024xy, hc689zy, htr025a, htr047a, htr256a, htr478a, htr569a, htr789a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hd37b, hd45a, htr145a, htr147a, htr378a, htr478a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc024xy, hc467yz, htr025a, htr048a, htr147a, htr148a, htr256a, htr567a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      rcases m.htr 4 8 10 (by decide) (by decide) with
        ⟨htr4810a, htr4810b, htr4810c, _, _⟩ | ⟨htr4810a, htr4810b, htr4810c, _, _⟩
      ·
        linarith only [hlam, hc012yx, hc468yz, htr018a, htr025a, htr1810a, htr256a, htr4810a, htr568a]
      ·
        linarith only [hlam, hc012yx, hc6810zy, htr014a, htr025a, htr148a, htr256a, htr4810a, htr5610a]

theorem shard_406 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237b : m.d 2 3 < m.d 2 7)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr348b : m.d 4 8 < m.d 3 8)
    : False :=
  proof_shard_406 m htr014a htr017a htr018a htr023c htr025a htr034b htr135a htr136a htr145a htr234a htr235a htr235b htr235c htr236a htr236b htr236c htr237a htr237b htr347a htr348a htr348b

#print axioms shard_406
end Jsp404.NoSatElevenDBMTerminal
