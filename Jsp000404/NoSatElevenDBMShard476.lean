import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_476 {lam p : ℝ} (m : ElevenModel lam p)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, htr134c, htr137b, htr147c])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, htr135c, htr137b, htr157c])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, htr136c, htr137b, htr167c])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, htr134b, htr147a, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc234zy, htr134a, htr137a, htr247a, htr347c])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc457xy, htr134a, htr137a, htr345a, htr347c])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hc467xy, htr134a, htr137a, htr346a, htr347c])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, htr135b, htr157a, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc235zy, htr135a, htr137a, htr257a, htr357c])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc567xy, htr135a, htr137a, htr356a, htr357c])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, htr136b, htr167a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hc678yx, htr136a, htr137a, htr367c, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hc679yx, htr136a, htr137a, htr367c, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, hc6710yx, htr136a, htr137a, htr3610a, htr367c])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc345yz, htr135a, htr137a, htr357c, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hc346yz, htr136a, htr137a, htr367c, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hc356yz, htr136a, htr137a, htr367c, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  rcases m.htr 4 5 6 (by decide) (by decide) with
    ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
  ·
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr124a, htr245a, htr456a, htr567a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd34a, hd67b, htr245a, htr246a, htr345a, htr467a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hd34a, hd57b, htr256a, htr257a, htr345a, htr456a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd36a, hd47b, htr246a, htr247a, htr368a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd36a, hd47b, htr246a, htr247a, htr369a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
      linarith only [hlam, hd36a, hd47b, htr246a, htr247a, htr3610a, htr4610a])
    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd34a, hd78b, htr245a, htr247a, htr345a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd34a, hd47b, htr134a, htr137a, htr378a, htr478a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc347xy, htr134a, htr137b, htr178a, htr378a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd34a, hd79b, htr245a, htr247a, htr345a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd34a, hd47b, htr134a, htr137a, htr379a, htr479a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hc347xy, htr134a, htr137b, htr179a, htr379a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd34a, hd67b, htr346a, htr468a, htr567a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hd34a, hd67b, htr346a, htr469a, htr567a, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
      linarith only [hlam, hd34a, hd67b, htr346a, htr4610a, htr5610a, htr567a])
    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd34a, hd89b, htr345a, htr456a, htr568a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
      linarith only [hlam, hd34a, hd910b, htr345a, htr456a, htr569a, htr6910a])
    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
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
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hd35a, hd47b, htr245a, htr247a, htr356a, htr456a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd34a, hd57b, htr245a, htr246a, htr346a, htr457a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd35a, hd67b, htr356a, htr467a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hc345yz, htr356b, htr369a, htr456a, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd35a, hd67b, htr356a, htr467a, htr469a, htr569a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
      linarith only [hlam, hc345yz, htr356b, htr3610a, htr456a, htr5610a])
    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
      linarith only [hlam, hd35a, hd67b, htr356a, htr4610a, htr467a, htr5610a])
    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd35a, hd78b, htr356a, htr456a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd34a, hd57b, htr134a, htr137a, htr378a, htr578a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc347xy, htr134a, htr137b, htr178a, htr378a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd35a, hd79b, htr356a, htr456a, htr457a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd34a, hd57b, htr134a, htr137a, htr379a, htr579a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hc347xy, htr134a, htr137b, htr179a, htr379a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd12a, hd89b, htr124a, htr246a, htr468a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
      linarith only [hlam, hd12a, hd910b, htr124a, htr246a, htr469a, htr6910a])
    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, hc012yx, hc689zy, htr017a, htr024a, htr178a, htr246a, htr469a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hc012yx, hc6910zy, htr017a, htr024a, htr179a, htr246a, htr4610a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
    ·
      linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]

theorem shard_476 {lam p : ℝ} (m : ElevenModel lam p)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    : False :=
  proof_shard_476 m htr017a htr024a htr025a htr124a htr134a htr134b htr134c htr135a htr135b htr135c htr136a htr136b htr136c htr137a htr137b

#print axioms shard_476
end Jsp404.NoSatElevenDBMTerminal
