import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_424 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr029a : m.d 0 2 + lam ≤ m.d 2 9)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr056a : m.d 5 6 + lam ≤ m.d 0 5)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr057a : m.d 5 7 + lam ≤ m.d 0 5)
    (htr057b : m.d 5 7 < m.d 0 7)
    (htr058a : m.d 5 8 + lam ≤ m.d 0 5)
    (htr058c : m.d 0 8 < m.d 0 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr146a : m.d 4 6 + lam ≤ m.d 1 4)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr157a : m.d 5 7 + lam ≤ m.d 1 5)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr458b : m.d 5 8 < m.d 4 8)
    (htr459b : m.d 5 9 < m.d 4 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd03a := (m.hrange 0 3 (by decide)).1
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
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
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
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
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc457yx, htr034a, htr037a, htr345a, htr347b])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc456yx, htr046a, htr047a, htr345a, htr347a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, hc456yx, htr146a, htr147a, htr345a, htr347a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, htr234b, htr247a, htr347a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  rcases m.htr 3 4 8 (by decide) (by decide) with
    ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
  ·
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, htr034c, htr048a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, htr046c, htr048b, htr068c])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, htr047c, htr048b, htr078c])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, htr046b, htr068a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc678xy, htr034c, htr046a, htr348a, htr467a, htr468c])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc456yx, htr245a, htr246c, htr267a, htr467a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, htr047b, htr078a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hc789yx, htr034c, htr047a, htr348a, htr478c, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hc457yx, htr245a, htr247c, htr279a, htr479a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hc467yz, htr347a, htr348a, htr478c, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd12a, hd78b, htr127a, htr279a, htr678a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hc023yz, hc789zy, htr035c, htr036a, htr058a, htr235a, htr236b, htr267a, htr589a, htr679a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
      linarith only [hlam, hc023yz, hc578yz, htr035c, htr036a, htr058c, htr089a, htr235a, htr236b, htr267a, htr589a, htr678a])
    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc468xy, htr046a, htr048b, htr089a, htr489a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd12a, hd89b, htr126a, htr267a, htr678a, htr789a]
    ·
      linarith only [hlam, hd13a, hd78b, htr134a, htr348a, htr489a, htr789a]
  ·
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc458yx, htr034a, htr038a, htr345a, htr348b])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc456yx, htr046a, htr048a, htr345a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, hc456yx, htr146a, htr148a, htr345a, htr348a])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr248a, htr248b, htr248c, _, _⟩
      linarith only [hlam, htr234b, htr248a, htr348a])
    obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
    rcases m.htr 3 4 9 (by decide) (by decide) with
      ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
    ·
      have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr049a, htr049b, htr049c, _, _⟩
        linarith only [hlam, htr034c, htr049a, htr349a])
      obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, htr046c, htr049b, htr069c])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, htr047c, htr049b, htr079c])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
        linarith only [hlam, htr048c, htr049b, htr089c])
      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, htr046b, htr069a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc679xy, htr034c, htr046a, htr349a, htr467a, htr469c])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc456yx, htr245a, htr246c, htr267a, htr467a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, htr047b, htr079a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc789xy, htr034c, htr047a, htr349a, htr478a, htr479c])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, htr048b, htr089a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc467yz, htr347a, htr349a, htr479c, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd12a, hd79b, htr127a, htr278a, htr678a, htr679a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd12a, hd89b, htr126a, htr267a, htr678a, htr789a]
      ·
        linarith only [hlam, hc478yz, htr348a, htr349a, htr489c, htr789a]
    ·
      have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr039a, htr039b, htr039c, _, _⟩
        linarith only [hlam, hc459yx, htr034a, htr039a, htr345a, htr349b])
      obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
      have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr249a, htr249b, htr249c, _, _⟩
        linarith only [hlam, htr234b, htr249a, htr349a])
      obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
      rcases m.htr 3 4 10 (by decide) (by decide) with
        ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
      ·
        have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
          linarith only [hlam, htr034c, htr0410a, htr3410a])
        obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
        have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
          linarith only [hlam, htr0410b, htr046c, htr0610c])
        obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
          linarith only [hlam, htr0410b, htr047c, htr0710c])
        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
          linarith only [hlam, htr0410b, htr048c, htr0810c])
        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
        have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
          linarith only [hlam, htr046b, htr0610a, htr4610a])
        obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc6710xy, htr034c, htr046a, htr3410a, htr4610c, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc456yx, htr245a, htr246c, htr267a, htr467a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, htr047b, htr0710a, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc7810xy, htr034c, htr047a, htr3410a, htr4710c, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, htr048b, htr0810a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          linarith only [hlam, hc467yz, htr3410a, htr347a, htr4710c, htr6710a])
        obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12a, hd710b, htr127a, htr278a, htr6710a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd810b, htr126a, htr267a, htr678a, htr7810a]
        ·
          linarith only [hlam, hc478yz, htr3410a, htr348a, htr4810c, htr7810a]
      ·
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd23b, hd56a, htr234a, htr346a, htr467a, htr567a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc456yx, htr036c, htr067a, htr345a, htr346c, htr467a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc456yx, htr245a, htr246c, htr267a, htr467a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          rcases m.htr 3 6 8 (by decide) (by decide) with
            ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, htr036c, htr068a, htr368a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            rcases m.htr 3 6 9 (by decide) (by decide) with
              ⟨htr369a, htr369b, htr369c, _, _⟩ | ⟨htr369a, htr369b, htr369c, _, _⟩
            ·
              rcases m.htr 3 6 10 (by decide) (by decide) with
                ⟨htr3610a, htr3610b, htr3610c, _, _⟩ | ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              ·
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc023yz, hc789yx, htr036a, htr234a, htr236b, htr267a, htr347a, htr479a, htr678a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc457yx, htr245a, htr247c, htr279a, htr479a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc023yz, hc7810yx, htr036a, htr234a, htr236b, htr267a, htr347a, htr4710a, htr678a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                    linarith only [hlam, hc457yx, htr245a, htr247c, htr2710a, htr4710a])
                  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd12a, hd78b, htr127a, htr279a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc023yz, hc789zy, htr036a, htr234a, htr236b, htr267a, htr348a, htr489a, htr679a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc458yx, htr245a, htr248c, htr289a, htr489a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd12a, hd78b, htr127a, htr2710a, htr6710a, htr678a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc023yz, hc7910zy, htr036a, htr234a, htr236b, htr267a, htr349a, htr4910a, htr6710a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd12a, hd89b, htr126a, htr267a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd12a, hd910b, htr126a, htr267a, htr679a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd12a, hd79b, htr128a, htr289a, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hc478yz, htr489b, htr4910a, htr789a, htr8910a]
                ·
                  rcases m.htr 5 7 8 (by decide) (by decide) with
                    ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                  ·
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hd23b, hd57a, htr234a, htr347a, htr478a, htr578a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hc457yx, htr037c, htr078a, htr345a, htr347c, htr478a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hd12a, hd79b, htr127a, htr278a, htr678a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    rcases m.htr 5 7 9 (by decide) (by decide) with
                      ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                    ·
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, hc567yz, htr078a, htr079a, htr579a, htr678a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, hc567yz, htr278a, htr279a, htr579a, htr678a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      rcases m.htr 5 7 10 (by decide) (by decide) with
                        ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                      ·
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                            linarith only [hlam, hc023yz, hc8910yx, htr037a, htr234a, htr237b, htr278a, htr348a, htr4810a, htr789a])
                          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                          have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                            linarith only [hlam, hc458yx, htr245a, htr248c, htr2810a, htr4810a])
                          obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                            linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
                          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                            linarith only [hlam, hd12a, hd89b, htr128a, htr2810a, htr6810a, htr689a])
                          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                            linarith only [hlam, hc023yz, hc8910zy, htr036a, htr234a, htr349a, htr368a, htr4910a, htr6810a])
                          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                            linarith only [hlam, hc567yz, htr459b, htr4910a, htr579b, htr679a, htr7910a])
                          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd12a, hd910b, htr127a, htr278a, htr789a, htr8910a]
                          ·
                            linarith only [hlam, hd12a, hd89b, htr127a, htr279a, htr7910a, htr8910a]
                        ·
                          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                            linarith only [hlam, hc567yz, htr458b, htr489a, htr578b, htr678a, htr789a])
                          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                            linarith only [hlam, hc023yz, hc8910xy, htr037a, htr234a, htr237b, htr278a, htr348a, htr489a, htr7810a])
                          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                            linarith only [hlam, hc567yz, htr458b, htr4810a, htr578b, htr678a, htr7810a])
                          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                            linarith only [hlam, hc023yz, hc8910yz, htr036a, htr234a, htr348a, htr369a, htr4810a, htr6910a])
                          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                            linarith only [hlam, hc012yx, hc689zy, htr014a, htr029a, htr148a, htr2910a, htr489a, htr6910a])
                          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                            linarith only [hlam, hc459yx, htr245a, htr249c, htr2910a, htr4910a])
                          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd23b, hd89a, htr234a, htr349a, htr4910a, htr8910a]
                          ·
                            linarith only [hlam, hd23b, hd910a, htr234a, htr348a, htr489a, htr8910a]
                      ·
                        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                          linarith only [hlam, htr057b, htr0710a, htr5710a])
                        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, htr0710c, htr078b, htr0810b])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                          linarith only [hlam, htr0710c, htr079b, htr0910b])
                        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                          linarith only [hlam, hc458yx, htr038c, htr0810a, htr345a, htr348c, htr4810a])
                        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                          linarith only [hlam, hc459yx, htr039c, htr0910a, htr345a, htr349c, htr4910a])
                        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                          linarith only [hlam, hc023yz, hc8910yx, htr037a, htr234a, htr237b, htr278a, htr348a, htr4810a, htr789a])
                        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc567yz, htr458b, htr489a, htr578b, htr678a, htr789a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd23b, hd89a, htr234a, htr349a, htr4910a, htr8910a]
                        ·
                          linarith only [hlam, hd23b, hd910a, htr234a, htr348a, htr489a, htr8910a]
                    ·
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, htr057b, htr079a, htr579a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, htr078b, htr079c, htr089b])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                        linarith only [hlam, htr027c, htr057b, htr279a, htr579a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc458yx, htr038c, htr089a, htr345a, htr348c, htr489a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                        linarith only [hlam, hc023yz, hc8910xy, htr037a, htr234a, htr237b, htr278a, htr348a, htr489a, htr7810a])
                      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                        linarith only [hlam, hc567yz, htr458b, htr4810a, htr578b, htr678a, htr7810a])
                      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                        linarith only [hlam, hc023yz, hc8910yz, htr036a, htr234a, htr348a, htr369a, htr4810a, htr6910a])
                      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                      have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                        linarith only [hlam, hc012yx, hc679zy, htr015a, htr029a, htr157a, htr2910a, htr579a, htr6910a])
                      obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd67b, hd89a, htr278a, htr279c, htr2910a, htr678a, htr8910a]
                      ·
                        linarith only [hlam, hd23b, hd910a, htr234a, htr348a, htr489a, htr8910a]
                  ·
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd23b, hd89a, htr035c, htr057a, htr235a, htr578a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hd23b, hd78a, htr234a, htr348a, htr489a, htr789a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hc458yx, htr245a, htr248c, htr289a, htr489a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hc012yx, hc678zy, htr015a, htr028a, htr157a, htr289a, htr578a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hc023yz, hc789yz, htr036a, htr234a, htr347a, htr368a, htr479a, htr689a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                      linarith only [hlam, hc023yz, hc8910yx, htr036a, htr234a, htr348a, htr368a, htr4810a, htr689a])
                    obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                      linarith only [hlam, hc458yx, htr245a, htr248c, htr2810a, htr4810a])
                    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc012yx, hc678zy, htr015a, htr028a, htr157a, htr2810a, htr578a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                      linarith only [hlam, hc023yz, hc8910zy, htr036a, htr234a, htr349a, htr368a, htr4910a, htr6810a])
                    obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hc789xy, htr457b, htr479b, htr4910a, htr578a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd03a, hd910b, htr036a, htr368a, htr689a, htr8910a]
                    ·
                      linarith only [hlam, hd78a, hd89b, htr457b, htr479a, htr578a, htr7910a, htr8910a]
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, hc023yz, htr036b, htr0610a, htr234a, htr346c, htr3610a])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                  linarith only [hlam, htr0610c, htr067b, htr0710b])
                obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0610c, htr068b, htr0810b])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                  linarith only [hlam, hc456yx, htr345a, htr346c, htr3610a, htr4610a])
                obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                  linarith only [hlam, hc457yx, htr037c, htr0710a, htr345a, htr347c, htr4710a])
                obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc458yx, htr038c, htr0810a, htr345a, htr348c, htr4810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc023yz, hc7810yx, htr036a, htr234a, htr236b, htr267a, htr347a, htr4710a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc6710yx, htr4610a, htr467b, htr478a, htr678a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 7 8 10 (by decide) (by decide) with
                  ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                ·
                  linarith only [hlam, hd23b, hd78a, htr234a, htr348a, htr4810a, htr7810a]
                ·
                  linarith only [hlam, hd23b, hd810a, htr234a, htr347a, htr478a, htr7810a]
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc023yz, htr036b, htr069a, htr234a, htr346c, htr369a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, htr067b, htr069c, htr079b])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, htr068b, htr069c, htr089b])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hc456yx, htr345a, htr346c, htr369a, htr469a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc457yx, htr037c, htr079a, htr345a, htr347c, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc458yx, htr038c, htr089a, htr345a, htr348c, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc023yz, hc789yx, htr036a, htr234a, htr236b, htr267a, htr347a, htr479a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc679yx, htr467b, htr469a, htr478a, htr678a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd23b, hd78a, htr234a, htr348a, htr489a, htr789a]
              ·
                linarith only [hlam, hd23b, hd89a, htr234a, htr347a, htr478a, htr789a]
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc023yz, htr036b, htr068a, htr234a, htr346c, htr368a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr067b, htr068c, htr078b])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, htr236b, htr268a, htr368a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc456yx, htr345a, htr346c, htr368a, htr468a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc457yx, htr037c, htr078a, htr345a, htr347c, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hc023yz, hc789xy, htr036a, htr234a, htr236b, htr267a, htr347a, htr478a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc678yx, htr467b, htr468a, htr479a, htr679a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc023yz, hc7810xy, htr036a, htr234a, htr236b, htr267a, htr347a, htr478a, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hc678yx, htr467b, htr468a, htr4710a, htr6710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hd23b, hd89a, htr234a, htr346a, htr468a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr289a, htr289b, htr289c, _, _⟩
              linarith only [hlam, hc678yx, htr267a, htr268c, htr289a, htr689a])
            obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hd23b, hd910a, htr234a, htr347a, htr479a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hd23b, hd79a, htr234a, htr349a, htr4910a, htr7910a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
              linarith only [hlam, hc459yx, htr245a, htr249c, htr2910a, htr4910a])
            obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hc012yx, hc7910yz, htr014a, htr028a, htr147a, htr289a, htr4710a, htr8910a]
            ·
              linarith only [hlam, hc012yx, hc789yz, htr014a, htr029a, htr147a, htr2910a, htr479a, htr8910a]
        ·
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd23b, hd78a, htr035c, htr056a, htr235a, htr567a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd23b, hd67a, htr234a, htr347a, htr478a, htr678a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hd23b, hd79a, htr035c, htr056a, htr235a, htr567a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd23b, hd67a, htr234a, htr347a, htr479a, htr679a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hc457yx, htr245a, htr247c, htr279a, htr479a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          rcases m.htr 5 6 8 (by decide) (by decide) with
            ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hd23b, hd67a, htr036c, htr068a, htr234a, htr346c, htr567a, htr568a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hd45b, hd67a, htr245a, htr246c, htr268a, htr567a, htr568a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            rcases m.htr 5 6 9 (by decide) (by decide) with
              ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc678xy, htr068a, htr069a, htr567a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hc678xy, htr268a, htr269a, htr567a, htr569a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                rcases m.htr 5 8 9 (by decide) (by decide) with
                  ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
                ·
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc678xy, htr567a, htr568b, htr589a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc023yz, hc8910yx, htr036a, htr234a, htr236b, htr268a, htr348a, htr4810a, htr689a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc678xy, htr458b, htr4810a, htr567a, htr568b, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc023yz, hc8910zy, htr036a, htr234a, htr236b, htr268a, htr349a, htr4910a, htr6810a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc679xy, htr459b, htr4910a, htr567a, htr569b, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd67a, hd910b, htr567a, htr568a, htr689a, htr8910a]
                  ·
                    linarith only [hlam, hd67a, hd89b, htr567a, htr569a, htr6910a, htr8910a]
                ·
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc023yz, hc8910xy, htr035c, htr036a, htr058a, htr235a, htr236b, htr268a, htr589a, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc678xy, htr458b, htr4810a, htr567a, htr568b, htr6810a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc023yz, hc8910yz, htr036a, htr234a, htr236b, htr269a, htr348a, htr4810a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc679xy, htr459b, htr4910a, htr567a, htr569b, htr6910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd23b, hd89a, htr234a, htr349a, htr4910a, htr8910a]
                  ·
                    linarith only [hlam, hd23b, hd910a, htr035c, htr058a, htr235a, htr589a, htr8910a]
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, htr056b, htr0610a, htr5610a])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0610c, htr068b, htr0810b])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                  linarith only [hlam, htr0610c, htr069b, htr0910b])
                obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc458yx, htr038c, htr0810a, htr345a, htr348c, htr4810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc459yx, htr039c, htr0910a, htr345a, htr349c, htr4910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc023yz, hc8910yx, htr036a, htr234a, htr236b, htr268a, htr348a, htr4810a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc678xy, htr458b, htr489a, htr567a, htr568b, htr689a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd23b, hd89a, htr234a, htr349a, htr4910a, htr8910a]
                ·
                  linarith only [hlam, hd23b, hd910a, htr234a, htr348a, htr489a, htr8910a]
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, htr056b, htr069a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, htr068b, htr069c, htr089b])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, htr026c, htr056b, htr269a, htr569a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc458yx, htr038c, htr089a, htr345a, htr348c, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc023yz, hc8910xy, htr036a, htr234a, htr236b, htr268a, htr348a, htr489a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hc678xy, htr458b, htr4810a, htr567a, htr568b, htr6810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd23b, hd910a, htr035c, htr056a, htr235a, htr569a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                linarith only [hlam, hc689yx, htr268a, htr269c, htr2910a, htr6910a])
              obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc023yz, hc8910yz, htr037a, htr234a, htr237b, htr279a, htr348a, htr4810a, htr7910a]
              ·
                linarith only [hlam, hc012yx, hc679yz, htr015a, htr029a, htr156a, htr2910a, htr569a, htr7910a]
          ·
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hd23b, hd89a, htr035c, htr056a, htr235a, htr568a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hd23b, hd68a, htr234a, htr348a, htr489a, htr689a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr289a, htr289b, htr289c, _, _⟩
              linarith only [hlam, hc458yx, htr245a, htr248c, htr289a, htr489a])
            obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
            have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
              linarith only [hlam, hd23b, hd810a, htr035c, htr056a, htr235a, htr568a, htr6810a])
            obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
            have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
              linarith only [hlam, hd23b, hd68a, htr234a, htr348a, htr4810a, htr6810a])
            obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
            have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
              linarith only [hlam, hc458yx, htr245a, htr248c, htr2810a, htr4810a])
            obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc012yx, hc678yz, htr015a, htr028a, htr156a, htr289a, htr568a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr469a, htr469b, htr469c, _, _⟩
              linarith only [hlam, hc012yx, hc689yz, htr014a, htr027a, htr146a, htr278a, htr469a, htr789a])
            obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc012yx, hc678yz, htr015a, htr028a, htr156a, htr2810a, htr568a, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hc023yz, hc8910zy, htr037a, htr234a, htr237b, htr278a, htr349a, htr4910a, htr7810a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc679xy, htr456b, htr469b, htr4910a, htr567a, htr6910a])
            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd910b, htr127a, htr278a, htr789a, htr8910a]
            ·
              linarith only [hlam, hd67a, hd89b, htr456b, htr469a, htr567a, htr6910a, htr8910a]

theorem shard_424 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr029a : m.d 0 2 + lam ≤ m.d 2 9)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr056a : m.d 5 6 + lam ≤ m.d 0 5)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr057a : m.d 5 7 + lam ≤ m.d 0 5)
    (htr057b : m.d 5 7 < m.d 0 7)
    (htr058a : m.d 5 8 + lam ≤ m.d 0 5)
    (htr058c : m.d 0 8 < m.d 0 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr146a : m.d 4 6 + lam ≤ m.d 1 4)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr157a : m.d 5 7 + lam ≤ m.d 1 5)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr457b : m.d 5 7 < m.d 4 7)
    (htr458b : m.d 5 8 < m.d 4 8)
    (htr459b : m.d 5 9 < m.d 4 9)
    : False :=
  proof_shard_424 m htr014a htr015a htr026c htr027a htr027c htr028a htr029a htr034a htr034c htr035c htr036a htr036b htr036c htr046a htr046b htr046c htr056a htr056b htr057a htr057b htr058a htr058c htr126a htr127a htr128a htr134a htr146a htr156a htr157a htr234a htr234b htr235a htr236b htr237b htr245a htr246c htr345a htr346a htr346c htr347a htr347b htr347c htr456b htr457b htr458b htr459b

#print axioms shard_424
end Jsp404.NoSatElevenDBMTerminal
