import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_081 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  obtain ⟨hd48a, hd48braw⟩ := m.hrange 4 8 (by decide)
  have hd48b : m.d 4 8 < 4*lam := by
    linarith only [hd48braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
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
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc026xy, hc026yx, hc026yz, hc026zy⟩ := endpoint_caps m 0 2 6 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc046xy, hc046yx, hc046yz, hc046zy⟩ := endpoint_caps m 0 4 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc258xy, hc258yx, hc258yz, hc258zy⟩ := endpoint_caps m 2 5 8 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc479xy, hc479yx, hc479yz, hc479zy⟩ := endpoint_caps m 4 7 9 (by decide) (by decide)
  obtain ⟨hc4710xy, hc4710yx, hc4710yz, hc4710zy⟩ := endpoint_caps m 4 7 10 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc4810xy, hc4810yx, hc4810yz, hc4810zy⟩ := endpoint_caps m 4 8 10 (by decide) (by decide)
  obtain ⟨hc4910xy, hc4910yx, hc4910yz, hc4910zy⟩ := endpoint_caps m 4 9 10 (by decide) (by decide)
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, hc256yx, htr023a, htr026a, htr124a, htr125a, htr234b])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, hc257yx, htr023a, htr027a, htr124a, htr125a, htr234b])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hc258yx, htr023a, htr028a, htr124a, htr125a, htr234b])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, htr124c, htr125b, htr145c])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, htr124b, htr145a, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hc456yx, htr124a, htr125a, htr245c, htr246a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc457yx, htr124a, htr125a, htr245c, htr247a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc458yx, htr124a, htr125a, htr245c, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, hc459yx, htr124a, htr125a, htr245c, htr249a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
    linarith only [hlam, hc4510yx, htr124a, htr125a, htr2410a, htr245c])
  obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd02a, hd56b, htr023a, htr123a, htr125a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hd02a, hd57b, htr023a, htr123a, htr125a, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hd02a, hd58b, htr023a, htr123a, htr125a, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc234yz, htr124a, htr125a, htr245c, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hd02a, hd45b, htr024a, htr246a, htr345a, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hd02a, hd45b, htr024a, htr247a, htr345a, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hd02a, hd45b, htr024a, htr248a, htr345a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, hd02a, hd45b, htr024a, htr249a, htr345a, htr349a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, hd02a, hd45b, htr024a, htr2410a, htr3410a, htr345a])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, htr245c, htr256a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, htr245c, htr257a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd02a, hd67b, htr023a, htr234a, htr346a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hd02a, hd68b, htr023a, htr234a, htr346a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hd02a, hd69b, htr023a, htr234a, htr346a, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hd02a, hd610b, htr023a, htr234a, htr346a, htr4610a])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hd02a, hd78b, htr023a, htr234a, htr347a, htr478a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
    linarith only [hlam, hd02a, hd79b, htr023a, htr234a, htr347a, htr479a])
  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
    linarith only [hlam, hd02a, hd710b, htr023a, htr234a, htr347a, htr4710a])
  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
    linarith only [hlam, hd02a, hd89b, htr023a, htr234a, htr348a, htr489a])
  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
    linarith only [hlam, hd02a, hd810b, htr023a, htr234a, htr348a, htr4810a])
  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
    linarith only [hlam, hd02a, hd910b, htr023a, htr234a, htr349a, htr4910a])
  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
  rcases m.htr 1 2 6 (by decide) (by decide) with
    ⟨htr126a, htr126b, htr126c, _, _⟩ | ⟨htr126a, htr126b, htr126c, _, _⟩
  ·
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hd02a, hd46b, htr023a, htr123a, htr126b, htr167a, htr467a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hd02a, hd46b, htr023a, htr123a, htr126b, htr168a, htr468a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
      linarith only [hlam, hd02a, hd46b, htr023a, htr123a, htr126b, htr169a, htr469a])
    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
    have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
      linarith only [hlam, hd02a, hd46b, htr023a, htr123a, htr126b, htr1610a, htr4610a])
    obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, htr126c, htr167a, htr267a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, htr126c, htr168a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, htr126c, htr169a, htr269a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
      linarith only [hlam, htr126c, htr1610a, htr2610a])
    obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
    rcases m.htr 1 2 7 (by decide) (by decide) with
      ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
    ·
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hd02a, hd47b, htr023a, htr123a, htr127b, htr178a, htr478a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hd02a, hd47b, htr023a, htr123a, htr127b, htr179a, htr479a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
        linarith only [hlam, hd02a, hd47b, htr023a, htr123a, htr127b, htr1710a, htr4710a])
      obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr127c, htr178a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, htr127c, htr179a, htr279a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, htr127c, htr1710a, htr2710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      rcases m.htr 1 2 8 (by decide) (by decide) with
        ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
      ·
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hd02a, hd48b, htr023a, htr123a, htr128b, htr189a, htr489a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hd02a, hd48b, htr023a, htr123a, htr128b, htr1810a, htr4810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, htr128c, htr189a, htr289a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, htr128c, htr1810a, htr2810a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        rcases m.htr 1 2 9 (by decide) (by decide) with
          ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
        ·
          rcases m.htr 1 2 10 (by decide) (by decide) with
            ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
          ·
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc045yz, htr056a, htr456c, htr467a, htr567a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc456zy, htr056a, htr057a, htr467a, htr567c])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc456zy, htr467a, htr567b, htr579a, htr679a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc025xy, hc489zy, htr023a, htr057a, htr234a, htr349a, htr578a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc025xy, hc4910zy, htr023a, htr057a, htr234a, htr3410a, htr579a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
              ·
                linarith only [hlam, hc478zy, htr489a, htr789b, htr7910a, htr8910a]
            ·
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, hc046yz, htr067a, htr467c, htr478a, htr678a])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc467zy, htr067a, htr068a, htr478a, htr678c])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc467zy, htr478a, htr567a, htr568a, htr678c])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, hc467zy, htr068b, htr089a, htr478a, htr678b, htr789a])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, htr068c, htr069b, htr089c])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc025xy, hc489zy, htr023a, htr056a, htr234a, htr349a, htr568a, htr689a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  linarith only [hlam, hc026xy, hc4910zy, htr023a, htr068a, htr234a, htr3410a, htr689a, htr8910a])
                obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hc026xy, hc489zy, htr023a, htr069a, htr234a, htr349a, htr6910a, htr8910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 6 7 9 (by decide) (by decide) with
                  ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                ·
                  rcases m.htr 7 9 10 (by decide) (by decide) with
                    ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  ·
                    linarith only [hlam, hc467zy, htr479c, htr4910a, htr679a, htr7910a]
                  ·
                    linarith only [hlam, hc467zy, htr479a, htr679b, htr6910a, htr7910a]
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hd25b, hd79a, htr056a, htr057a, htr256a, htr567b, htr679a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  rcases m.htr 5 7 8 (by decide) (by decide) with
                    ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                  ·
                    linarith only [hlam, hc045yz, htr057a, htr457c, htr478a, htr578a]
                  ·
                    linarith only [hlam, hd25b, hd79a, htr257a, htr578a, htr678a, htr679a]
              ·
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc025xy, hc478zy, htr023a, htr056a, htr234a, htr348a, htr567a, htr678a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hd25b, hd78a, htr056a, htr057a, htr256a, htr567b, htr678a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc045yz, htr057a, htr457c, htr479a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hd25b, hd78a, htr257a, htr579a, htr678a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd25b, hd89a, htr256a, htr567a, htr678a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hd25b, hd910a, htr256a, htr567a, htr679a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
                ·
                  linarith only [hlam, hc478zy, htr489a, htr789b, htr7910a, htr8910a]
          ·
            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              linarith only [hlam, hc256zy, htr1210a, htr126a, htr2610b, htr5610a])
            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
            have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
              linarith only [hlam, hc257zy, htr1210a, htr127a, htr2710b, htr5710a])
            obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc267zy, htr1210a, htr127a, htr2710b, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc278zy, htr1210a, htr128a, htr2810b, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc045yz, htr056a, htr456c, htr467a, htr567a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hd25b, hd610a, htr056a, htr057a, htr257a, htr5610a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc025xy, hc4810zy, htr023a, htr057a, htr234a, htr3410a, htr578a, htr7810a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a]
              ·
                linarith only [hlam, hd46b, hd710a, htr467a, htr5710a, htr578a, htr678a]
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc025xy, hc4710zy, htr023a, htr056a, htr234a, htr3410a, htr567a, htr6710a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hd25b, hd710a, htr056a, htr057a, htr256a, htr5710a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc045yz, htr057a, htr457c, htr478a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd25b, hd710a, htr257a, htr578a, htr6710a, htr678a]
              ·
                linarith only [hlam, hd25b, hd810a, htr256a, htr567a, htr678a, htr7810a]
        ·
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc256zy, htr126a, htr129a, htr269b, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc257zy, htr127a, htr129a, htr279b, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc267zy, htr127a, htr129a, htr279b, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc278zy, htr128a, htr129a, htr289b, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc045yz, htr056a, htr456c, htr467a, htr567a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hd25b, hd69a, htr056a, htr057a, htr257a, htr569a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc025xy, hc489zy, htr023a, htr057a, htr234a, htr349a, htr578a, htr789a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a]
            ·
              linarith only [hlam, hd46b, hd79a, htr467a, htr578a, htr579a, htr678a]
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc025xy, hc479zy, htr023a, htr056a, htr234a, htr349a, htr567a, htr679a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hd25b, hd79a, htr056a, htr057a, htr256a, htr579a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc045yz, htr057a, htr457c, htr478a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd25b, hd79a, htr257a, htr578a, htr678a, htr679a]
            ·
              linarith only [hlam, hd25b, hd89a, htr256a, htr567a, htr678a, htr789a]
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc025yz, htr058a, htr125a, htr128a, htr258b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc026yz, htr068a, htr126a, htr128a, htr268b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc256zy, htr126a, htr128a, htr268b, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc267zy, htr127a, htr128a, htr278b, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc026xy, hc468zy, htr023a, htr067a, htr234a, htr348a, htr567a, htr568a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hd46b, hd89a, htr467a, htr567a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, hc468zy, htr068a, htr069a, htr489a, htr689c])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd46b, hd910a, htr067a, htr069a, htr467a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc468zy, htr489c, htr4910a, htr689a, htr8910a]
          ·
            linarith only [hlam, hc468zy, htr489a, htr689b, htr6910a, htr8910a]
        ·
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc025xy, hc478zy, htr023a, htr056a, htr234a, htr348a, htr567a, htr678a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd25b, hd89a, htr056a, htr058a, htr256a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, hc458zy, htr058a, htr059a, htr489a, htr589c])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd25b, hd910a, htr056a, htr059a, htr256a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc458zy, htr489c, htr4910a, htr589a, htr8910a]
          ·
            linarith only [hlam, hc458zy, htr489a, htr589b, htr5910a, htr8910a]
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc025yz, htr057a, htr125a, htr127a, htr257b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc256zy, htr126a, htr127a, htr267b, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd25b, hd67a, htr125a, htr127a, htr278a, htr678a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc457zy, htr057a, htr058a, htr258b, htr278c, htr478a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc467zy, htr478a, htr567a, htr568a, htr678c])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc467zy, htr478a, htr568b, htr589a, htr678b, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hd25b, hd89a, htr056a, htr058a, htr256a, htr589a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a]
        ·
          linarith only [hlam, hc025xy, hc489zy, htr023a, htr056a, htr234a, htr349a, htr568a, htr689a]
      ·
        rcases m.htr 0 5 6 (by decide) (by decide) with
          ⟨htr056a, htr056b, htr056c, _, _⟩ | ⟨htr056a, htr056b, htr056c, _, _⟩
        ·
          linarith only [hlam, hd25b, hd78a, htr056a, htr057a, htr256a, htr567b, htr678a]
        ·
          linarith only [hlam, hc025xy, hc478zy, htr023a, htr056a, htr234a, htr348a, htr567a, htr678a]
  ·
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, hc025yz, htr056a, htr125a, htr126a, htr256b])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc456zy, htr056a, htr057a, htr467a, htr567c])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd25b, hd56a, htr125a, htr126a, htr267a, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr127a, htr127b, htr127c, _, _⟩
        linarith only [hlam, hd02a, hd46b, htr023a, htr123a, htr127a, htr267c, htr467a])
      obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc456zy, htr057b, htr078a, htr467a, htr567b, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hc278zy, htr027c, htr078a, htr127a, htr128a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd25b, hd89a, htr027c, htr078a, htr125a, htr127a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hd25b, hd78a, htr125a, htr128a, htr289a, htr789a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd02a, hd46b, htr028a, htr289a, htr468a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc046yz, htr068a, htr468c, htr489a, htr689a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc468zy, htr068a, htr069a, htr489a, htr689c])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd25b, hd910a, htr026c, htr069a, htr125a, htr126a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
      ·
        linarith only [hlam, hc478zy, htr489a, htr679b, htr6910a, htr789b, htr8910a]
    ·
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd25b, hd78a, htr125a, htr126a, htr256b, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc467zy, htr056b, htr068a, htr478a, htr567a, htr678c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd25b, hd89a, htr026c, htr068a, htr125a, htr126a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a]
      ·
        linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a]

theorem shard_081 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    : False :=
  proof_shard_081 m htr023a htr024a htr123a htr124a htr124b htr124c htr125a htr125b htr234a htr234b

#print axioms shard_081
end Jsp404.NoSatElevenDBMTerminal
