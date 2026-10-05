import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_620 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd48a := (m.hrange 4 8 (by decide)).1
  have hd49a := (m.hrange 4 9 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
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
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc046xy, hc046yx, hc046yz, hc046zy⟩ := endpoint_caps m 0 4 6 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc359xy, hc359yx, hc359yz, hc359zy⟩ := endpoint_caps m 3 5 9 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc4710xy, hc4710yx, hc4710yz, hc4710zy⟩ := endpoint_caps m 4 7 10 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc4810xy, hc4810yx, hc4810yz, hc4810zy⟩ := endpoint_caps m 4 8 10 (by decide) (by decide)
  obtain ⟨hc4910xy, hc4910yx, hc4910yz, hc4910zy⟩ := endpoint_caps m 4 9 10 (by decide) (by decide)
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, htr013b, htr035a, htr123b, htr235a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced134 := (m.htr 1 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr134a, htr134b, htr134c, _, _⟩
    linarith only [hlam, hd01b, hd35a, htr013a, htr134a, htr234a, htr235a])
  obtain ⟨htr134a, htr134b, htr134c, _, _⟩ := hforced134
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, htr123b, htr135a, htr235a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, htr134b, htr135c, htr145b])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, htr134c, htr145a, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hc456xy, htr123b, htr134a, htr235a, htr345b, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hc345yx, htr234b, htr235a, htr246a, htr346a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc457xy, htr123b, htr134a, htr235a, htr345b, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc345yx, htr234b, htr235a, htr247a, htr347a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc458xy, htr123b, htr134a, htr235a, htr345b, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc345yx, htr234b, htr235a, htr248a, htr348a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, hc459xy, htr123b, htr134a, htr235a, htr345b, htr349a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, hc345yx, htr234b, htr235a, htr249a, htr349a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced3410 := (m.htr 3 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr3410a, htr3410b, htr3410c, _, _⟩
    linarith only [hlam, hc4510xy, htr123b, htr134a, htr235a, htr3410a, htr345b])
  obtain ⟨htr3410a, htr3410b, htr3410c, _, _⟩ := hforced3410
  have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
    linarith only [hlam, hc345yx, htr234b, htr235a, htr2410a, htr3410a])
  obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr123a, htr235a, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc345yx, htr134a, htr135c, htr156a, htr356a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr125b, htr156a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hd01b, hd57a, htr012a, htr123a, htr235a, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hd01b, hd59a, htr012a, htr123a, htr235a, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, htr345b, htr356a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, htr345b, htr357a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd01b, hd67a, htr012a, htr124a, htr246a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd01b, hd46a, htr012a, htr126a, htr267a, htr467a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hd01b, hd68a, htr012a, htr124a, htr246a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd01b, hd46a, htr012a, htr126a, htr268a, htr468a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hd01b, hd69a, htr012a, htr124a, htr246a, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd01b, hd46a, htr012a, htr126a, htr269a, htr469a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hd01b, hd610a, htr012a, htr124a, htr246a, htr4610a])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hd01b, hd46a, htr012a, htr126a, htr2610a, htr4610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hd01b, hd78a, htr012a, htr124a, htr247a, htr478a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hd01b, hd47a, htr012a, htr127a, htr278a, htr478a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
    linarith only [hlam, hd01b, hd79a, htr012a, htr124a, htr247a, htr479a])
  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
    linarith only [hlam, hd01b, hd710a, htr012a, htr124a, htr247a, htr4710a])
  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
    linarith only [hlam, hd01b, hd47a, htr012a, htr127a, htr2710a, htr4710a])
  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
    linarith only [hlam, hd01b, hd89a, htr012a, htr124a, htr248a, htr489a])
  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
    linarith only [hlam, hd01b, hd48a, htr012a, htr128a, htr289a, htr489a])
  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
    linarith only [hlam, hd01b, hd810a, htr012a, htr124a, htr248a, htr4810a])
  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
  have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
    linarith only [hlam, hd01b, hd48a, htr012a, htr128a, htr2810a, htr4810a])
  obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
    linarith only [hlam, hd01b, hd910a, htr012a, htr124a, htr249a, htr4910a])
  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
    linarith only [hlam, hd01b, hd49a, htr012a, htr129a, htr2910a, htr4910a])
  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
  rcases m.htr 2 3 6 (by decide) (by decide) with
    ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
  ·
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, hc345yx, htr134a, htr136a, htr235a, htr236a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hd01b, hd35a, htr016a, htr167a, htr235a, htr236b, htr267a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr136b, htr137c, htr167b])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc356xy, htr235a, htr236b, htr267a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc357xy, htr235a, htr236b, htr267b, htr278a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd35a, hd78b, htr235a, htr236a, htr367a, htr678a]
    ·
      linarith only [hlam, hd35a, hd67b, htr123b, htr137a, htr235a, htr378a, htr678a]
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr013b, htr036a, htr123b, htr236a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, htr236b, htr269a, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
      linarith only [hlam, htr236b, htr2610a, htr3610a])
    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
    rcases m.htr 0 3 4 (by decide) (by decide) with
      ⟨htr034a, htr034b, htr034c, _, _⟩ | ⟨htr034a, htr034b, htr034c, _, _⟩
    ·
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc345yx, htr034a, htr035c, htr056a, htr356a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc345yx, htr034a, htr036c, htr067a, htr235b, htr256b, htr267a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc345yx, htr034a, htr036c, htr068a, htr235b, htr256b, htr268a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc016yx, hc467yz, htr012a, htr068a, htr124a, htr247a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc015yx, hc478yz, htr012a, htr056a, htr124a, htr248a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc015yx, hc489yz, htr012a, htr056a, htr124a, htr249a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a]
        ·
          linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a]
      ·
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc016yx, hc468yz, htr012a, htr067a, htr124a, htr248a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc456yz, htr468b, htr489a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc016yx, hc489yz, htr012a, htr067a, htr124a, htr249a, htr678a, htr789a]
        ·
          linarith only [hlam, hc016yx, hc478yz, htr012a, htr068a, htr124a, htr248a, htr689a, htr789a]
    ·
      rcases m.htr 2 3 7 (by decide) (by decide) with
        ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
      ·
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc345yx, htr134a, htr137a, htr235a, htr237a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hd01b, hd35a, htr017a, htr178a, htr235a, htr237b, htr278a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, htr137b, htr138c, htr178b])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc357xy, htr235a, htr237b, htr278a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc358xy, htr235a, htr237b, htr278b, htr289a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd35a, hd89b, htr235a, htr237a, htr378a, htr789a]
        ·
          linarith only [hlam, hd35a, hd78b, htr123b, htr138a, htr235a, htr389a, htr789a]
      ·
        have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
          linarith only [hlam, htr237b, htr2710a, htr3710a])
        obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
        rcases m.htr 2 3 8 (by decide) (by decide) with
          ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
        ·
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc345yx, htr134a, htr138a, htr235a, htr238a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hd01b, hd35a, htr018a, htr189a, htr235a, htr238b, htr289a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr139a, htr139b, htr139c, _, _⟩
            linarith only [hlam, htr138b, htr139c, htr189b])
          obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc358xy, htr235a, htr238b, htr289a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hc359xy, htr235a, htr238b, htr289b, htr2910a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd35a, hd910b, htr235a, htr238a, htr389a, htr8910a]
          ·
            linarith only [hlam, hd35a, hd89b, htr123b, htr139a, htr235a, htr3910a, htr8910a]
        ·
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, htr238b, htr2810a, htr3810a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          rcases m.htr 2 3 9 (by decide) (by decide) with
            ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
          ·
            have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr059a, htr059b, htr059c, _, _⟩
              linarith only [hlam, hc035zy, htr059a, htr235a, htr239a, htr359c])
            obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
            have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
              linarith only [hlam, hc359xy, htr235a, htr239b, htr2910a, htr3910a])
            obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
            have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr569a, htr569b, htr569c, _, _⟩
              linarith only [hlam, hc356yz, htr236a, htr239a, htr369c, htr569a])
            obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
            have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
              linarith only [hlam, hd35a, hd59b, htr235a, htr239a, htr3910a, htr5910a])
            obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hd35a, hd910b, htr056a, htr059a, htr356a, htr5910a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            rcases m.htr 6 9 10 (by decide) (by decide) with
              ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            ·
              linarith only [hlam, hc015yx, hc4910yz, htr012a, htr056a, htr124a, htr2410a, htr569a, htr6910a]
            ·
              linarith only [hlam, hd35a, hd69b, htr235a, htr239a, htr3910a, htr6910a]
          ·
            rcases m.htr 2 3 10 (by decide) (by decide) with
              ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
            ·
              have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                linarith only [hlam, hc356yz, htr2310a, htr236a, htr3610c, htr5610a])
              obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
              have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                linarith only [hlam, hc357yz, htr2310a, htr237a, htr3710c, htr5710a])
              obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
              have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                linarith only [hlam, hc367yz, htr2310a, htr237a, htr3710c, htr6710a])
              obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc378yz, htr2310a, htr238a, htr3810c, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              rcases m.htr 5 6 7 (by decide) (by decide) with
                ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
              ·
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc015yx, hc4710yz, htr012a, htr056a, htr124a, htr2410a, htr567a, htr6710a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hd35a, hd710b, htr056a, htr057a, htr356a, htr5710a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc045zy, htr057a, htr457b, htr478a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd35a, hd810b, htr356a, htr567a, htr678a, htr7810a]
                ·
                  linarith only [hlam, hd35a, hd710b, htr357a, htr578a, htr6710a, htr678a]
              ·
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc045zy, htr056a, htr456b, htr467a, htr567a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hd35a, hd610b, htr056a, htr057a, htr357a, htr5610a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc015yx, hc4810yz, htr012a, htr057a, htr124a, htr2410a, htr578a, htr7810a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd46a, hd710b, htr467a, htr5710a, htr578a, htr678a]
                ·
                  linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a]
            ·
              rcases m.htr 5 6 7 (by decide) (by decide) with
                ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
              ·
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                    linarith only [hlam, hc015yx, hc478yz, htr012a, htr056a, htr124a, htr248a, htr567a, htr678a])
                  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hd35a, hd78b, htr056a, htr057a, htr356a, htr567c, htr678a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc045zy, htr057a, htr457b, htr479a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd35a, hd78b, htr357a, htr579a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd35a, hd89b, htr356a, htr567a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd35a, hd910b, htr356a, htr567a, htr679a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc478yz, htr489a, htr789c, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hc478yz, htr489b, htr4910a, htr789a, htr8910a]
                ·
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, hc046zy, htr067a, htr467b, htr478a, htr678a])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc467yz, htr067a, htr068a, htr478a, htr678b])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hc467yz, htr478a, htr567a, htr568a, htr678b])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, hc467yz, htr068c, htr089a, htr478a, htr678c, htr789a])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                    linarith only [hlam, htr068b, htr069c, htr089b])
                  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                    linarith only [hlam, hc015yx, hc489yz, htr012a, htr056a, htr124a, htr249a, htr568a, htr689a])
                  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                  have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    linarith only [hlam, hc016yx, hc4910yz, htr012a, htr068a, htr124a, htr2410a, htr689a, htr8910a])
                  obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc016yx, hc489yz, htr012a, htr069a, htr124a, htr249a, htr6910a, htr8910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 6 7 9 (by decide) (by decide) with
                    ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hd35a, hd79b, htr056a, htr057a, htr356a, htr567c, htr679a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    rcases m.htr 5 7 8 (by decide) (by decide) with
                      ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                    ·
                      linarith only [hlam, hd35a, hd79b, htr357a, htr578a, htr678a, htr679a]
                    ·
                      linarith only [hlam, hc045zy, htr057a, htr457b, htr478a, htr578a]
                  ·
                    rcases m.htr 7 9 10 (by decide) (by decide) with
                      ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    ·
                      linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a]
                    ·
                      linarith only [hlam, hc467yz, htr479b, htr4910a, htr679a, htr7910a]
              ·
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc045zy, htr056a, htr456b, htr467a, htr567a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc456yz, htr056a, htr057a, htr467a, htr567b])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc456yz, htr467b, htr479a, htr567a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc456yz, htr467a, htr567c, htr579a, htr679a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc015yx, hc489yz, htr012a, htr057a, htr124a, htr249a, htr578a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc015yx, hc4910yz, htr012a, htr057a, htr124a, htr2410a, htr579a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hc478yz, htr489a, htr789c, htr7910a, htr8910a]
                ·
                  linarith only [hlam, hc478yz, htr489b, htr4910a, htr789a, htr8910a]

theorem shard_620 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    : False :=
  proof_shard_620 m htr012a htr013a htr013b htr016a htr017a htr018a htr123a htr123b htr124a htr125b htr126a htr127a htr128a htr129a htr234a htr234b htr235a htr235b

#print axioms shard_620
end Jsp404.NoSatElevenDBMTerminal
