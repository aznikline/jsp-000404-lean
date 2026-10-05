import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_603 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
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
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hc456yx, htr134a, htr136a, htr345a, htr346b])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, htr123b, htr136a, htr236a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr345b, htr346c, htr356b])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, htr345c, htr356a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc245yz, htr256a, htr345a, htr346a, htr456b])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc567xy, htr345a, htr346a, htr456b, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc568xy, htr345a, htr346a, htr456b, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc456yx, htr345b, htr346a, htr358a, htr458a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc569xy, htr345a, htr346a, htr456b, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hc456yx, htr345b, htr346a, htr359a, htr459a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd01b, hd67a, htr012a, htr125a, htr256a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr267a, htr567a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, htr236b, htr237c, htr267b])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd45b, hd56a, htr345a, htr346a, htr467a, htr567a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hc456yx, htr345a, htr346c, htr367a, htr467a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd01b, hd68a, htr012a, htr125a, htr256a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr268a, htr568a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, htr236b, htr238c, htr268b])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, hd23a, hd45b, htr134a, htr138a, htr238a, htr345a])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hd45b, hd56a, htr345a, htr346a, htr468a, htr568a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hc456yx, htr345a, htr346c, htr368a, htr468a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hd01b, hd69a, htr012a, htr125a, htr256a, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hd45b, hd56a, htr345a, htr346a, htr469a, htr569a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hc456yx, htr345a, htr346c, htr369a, htr469a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  rcases m.htr 3 4 7 (by decide) (by decide) with
    ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
  ·
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, htr134c, htr147a, htr347a])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr247a, htr247b, htr247c, _, _⟩
      linarith only [hlam, htr234c, htr247a, htr347a])
    obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
    rcases m.htr 2 4 6 (by decide) (by decide) with
      ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
    ·
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc023zy, htr034a, htr234b, htr246a, htr346a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc456yx, htr034a, htr036a, htr345a, htr346b])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd24a, hd78b, htr246a, htr346a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd24a, hd79b, htr246a, htr346a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hd24a, hd710b, htr246a, htr346a, htr347a, htr4710a])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd24a, hd89b, htr246a, htr346a, htr348a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, htr468c, htr489a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 1 4 6 (by decide) (by decide) with
          ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
        ·
          rcases m.htr 2 5 7 (by decide) (by decide) with
            ⟨htr257a, htr257b, htr257c, _, _⟩ | ⟨htr257a, htr257b, htr257c, _, _⟩
          ·
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd47b, hd56a, htr256a, htr257a, htr478a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc567xy, htr256a, htr257b, htr278a, htr578a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd47b, hd56a, htr256a, htr257a, htr479a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, hc567xy, htr256a, htr257b, htr279a, htr579a])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
              linarith only [hlam, hd47b, hd56a, htr256a, htr257a, htr4710a, htr5710a])
            obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, hc567xy, htr256a, htr257b, htr2710a, htr5710a])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc013yx, hc7910yz, htr012a, htr036a, htr127a, htr2710a, htr369a, htr6910a])
            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hd01b, hd910a, htr012a, htr127a, htr279a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
            ·
              linarith only [hlam, hc478zy, htr489a, htr789b, htr7910a, htr8910a]
          ·
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr258a, htr258b, htr258c, _, _⟩
              linarith only [hlam, hc457zy, htr257a, htr258a, htr478a, htr578c])
            obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hc457zy, htr478c, htr489a, htr578a, htr789a]
            ·
              linarith only [hlam, hc457zy, htr478a, htr578b, htr589a, htr789a]
        ·
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc456yx, htr145b, htr146a, htr157a, htr457a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc456yx, htr145b, htr146a, htr158a, htr458a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc467xy, htr146a, htr147b, htr178a, htr478a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hd01b, hd56a, htr015a, htr157a, htr256a, htr257a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr258a, htr258b, htr258c, _, _⟩
            linarith only [hlam, hd01b, hd56a, htr015a, htr158a, htr256a, htr258a])
          obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hc457zy, htr478c, htr489a, htr578a, htr789a]
          ·
            linarith only [hlam, hd01b, hd58a, htr017a, htr178a, htr589a, htr789a]
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc245yz, htr258a, htr345a, htr348a, htr458b])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc247yz, htr278a, htr347a, htr348a, htr478b])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc457zy, htr347a, htr348a, htr478b, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd47b, hd56a, htr256a, htr257a, htr479a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hd45b, hd78a, htr278a, htr279a, htr457a, htr579a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd45b, hd58a, htr345a, htr348a, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc458yx, htr345a, htr348c, htr389a, htr489a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc013yx, hc789yz, htr012a, htr036a, htr127a, htr279a, htr368a, htr689a]
        ·
          linarith only [hlam, hc013yx, hc568yz, htr012a, htr036a, htr125a, htr258a, htr368b, htr389a, htr689a]
    ·
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc456yx, htr245b, htr246a, htr257a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, hc456yx, htr245b, htr246a, htr258a, htr458a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr278a, htr578a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hd01b, hd46a, htr017a, htr178a, htr246a, htr247b, htr278a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr147b, htr148c, htr178b])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc467xy, htr246a, htr247b, htr278a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc013yx, hc578yz, htr012a, htr034a, htr125a, htr258a, htr347a, htr478a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc456yx, htr034a, htr035a, htr345c, htr346a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc023zy, hc578yz, htr035a, htr138c, htr189a, htr234a, htr347a, htr358c, htr478a, htr589a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc468xy, htr128b, htr189a, htr246a, htr247b, htr278b, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
      ·
        linarith only [hlam, hd46a, hd78b, htr124b, htr148a, htr246a, htr489a, htr789a]
  ·
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc245yz, htr257a, htr345a, htr347a, htr457b])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd45b, hd57a, htr345a, htr347a, htr478a, htr578a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc457yx, htr345a, htr347c, htr378a, htr478a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd01b, hd79a, htr012a, htr125a, htr257a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd45b, hd57a, htr345a, htr347a, htr479a, htr579a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hc457yx, htr345a, htr347c, htr379a, htr479a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
      linarith only [hlam, hd01b, hd710a, htr012a, htr125a, htr257a, htr5710a])
    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
      linarith only [hlam, hd45b, hd57a, htr345a, htr347a, htr4710a, htr5710a])
    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
      linarith only [hlam, hc457yx, htr345a, htr347c, htr3710a, htr4710a])
    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd23a, hd78b, htr237a, htr379a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        linarith only [hlam, hd23a, hd78b, htr237a, htr3710a, htr6710a, htr678a])
      obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd13a, hd89b, htr136a, htr367a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd13a, hd910b, htr136a, htr367a, htr679a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 2 4 6 (by decide) (by decide) with
        ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
      ·
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hc023zy, htr034a, htr234b, htr246a, htr347a, htr467b])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc456yx, htr034a, htr036a, htr345a, htr346b])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc013yx, hc578yz, htr012a, htr036a, htr125a, htr258a, htr367a, htr678a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc013yx, hc789zy, htr012a, htr036a, htr128a, htr289a, htr367a, htr679a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 5 8 9 (by decide) (by decide) with
          ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
        ·
          linarith only [hlam, hd56a, hd78b, htr256a, htr258a, htr589a, htr789a]
        ·
          linarith only [hlam, hc568xy, htr256a, htr258b, htr289a, htr589a]
      ·
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, hc456yx, htr125b, htr159a, htr245b, htr246a, htr459a])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc456yx, htr245b, htr246a, htr258a, htr458a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc013yx, hc578yz, htr012a, htr036a, htr125a, htr258a, htr367a, htr678a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hc456yx, htr034a, htr036a, htr345a, htr346b])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hc456yx, htr034a, htr035a, htr345c, htr346a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc013zy, hc7910zy, htr035a, htr135c, htr136a, htr159a, htr367a, htr5910a, htr6710a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]
    ·
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc013yx, hc567yz, htr012a, htr036a, htr125a, htr257a, htr367b, htr378a, htr678a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hc456yx, htr034a, htr036a, htr345a, htr346b])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hc456yx, htr034a, htr035a, htr345c, htr346a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc023zy, htr034c, htr045a, htr234a, htr345a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc467yz, htr034b, htr048a, htr347a, htr478c, htr678a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr246a, htr246b, htr246c, _, _⟩
        linarith only [hlam, hc023zy, htr034a, htr234b, htr246a, htr347a, htr467b])
      obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc456yx, htr045a, htr048a, htr246a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr259a, htr259b, htr259c, _, _⟩
        linarith only [hlam, hc023zy, hc567yz, htr035a, htr237a, htr257a, htr259a, htr359a, htr378a, htr678a])
      obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr012a, htr124a, htr248a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
        linarith only [hlam, hd01b, hd910a, htr012a, htr125a, htr259a, htr5910a])
      obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567yz, htr458b, htr489a, htr578b, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hd23a, hd910b, htr237a, htr378a, htr789a, htr8910a]
      ·
        linarith only [hlam, hd23a, hd89b, htr237a, htr379a, htr7910a, htr8910a]

theorem shard_603 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    : False :=
  proof_shard_603 m htr012a htr015a htr017a htr123b htr124a htr124b htr125a htr125b htr126a htr127a htr128a htr128b htr134a htr134c htr135c htr145b htr234a htr234b htr234c htr245b htr345a htr345b htr345c htr346a htr346b htr346c

#print axioms shard_603
end Jsp404.NoSatElevenDBMTerminal
