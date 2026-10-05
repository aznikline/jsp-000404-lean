import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_052 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr239b : m.d 3 9 < m.d 2 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < 4*lam := by
    linarith only [hd26braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
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
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc026xy, hc026yx, hc026yz, hc026zy⟩ := endpoint_caps m 0 2 6 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc279xy, hc279yx, hc279yz, hc279zy⟩ := endpoint_caps m 2 7 9 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc5710xy, hc5710yx, hc5710yz, hc5710zy⟩ := endpoint_caps m 5 7 10 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, htr124c, htr126b, htr146c])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr125c, htr126b, htr156c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr124b, htr146a, htr246a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc456xy, htr124a, htr126a, htr245a, htr246c])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr125b, htr156a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc567yx, htr125a, htr126a, htr256c, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc568yx, htr125a, htr126a, htr256c, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, hc569yx, htr125a, htr126a, htr256c, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, hc5610yx, htr125a, htr126a, htr2510a, htr256c])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd02a, hd67b, htr024a, htr124a, htr126a, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd02a, hd68b, htr024a, htr124a, htr126a, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd02a, hd69b, htr024a, htr124a, htr126a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hd02a, hd610b, htr024a, htr124a, htr126a, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc245yz, htr125a, htr126a, htr256c, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd02a, hd56b, htr025a, htr257a, htr456a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd02a, hd56b, htr025a, htr258a, htr456a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hd02a, hd56b, htr025a, htr259a, htr456a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hd02a, hd56b, htr025a, htr2510a, htr4510a, htr456a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, htr256c, htr267a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd02a, hd78b, htr024a, htr245a, htr457a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hd02a, hd79b, htr024a, htr245a, htr457a, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
    linarith only [hlam, hd02a, hd710b, htr024a, htr245a, htr457a, htr5710a])
  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
    linarith only [hlam, hd02a, hd89b, htr024a, htr245a, htr458a, htr589a])
  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
    linarith only [hlam, hd02a, hd810b, htr024a, htr245a, htr458a, htr5810a])
  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
    linarith only [hlam, hd02a, hd910b, htr024a, htr245a, htr459a, htr5910a])
  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
  rcases m.htr 1 2 7 (by decide) (by decide) with
    ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
  ·
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd02a, hd57b, htr024a, htr124a, htr127b, htr178a, htr578a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd02a, hd57b, htr024a, htr124a, htr127b, htr179a, htr579a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
      linarith only [hlam, hd02a, hd57b, htr024a, htr124a, htr127b, htr1710a, htr5710a])
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
        linarith only [hlam, hd02a, hd58b, htr024a, htr124a, htr128b, htr189a, htr589a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hd02a, hd58b, htr024a, htr124a, htr128b, htr1810a, htr5810a])
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
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hd02a, hd59b, htr024a, htr124a, htr129b, htr1910a, htr5910a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, htr129c, htr1910a, htr2910a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        rcases m.htr 1 2 10 (by decide) (by decide) with
          ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
        ·
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc056yz, htr067a, htr567c, htr578a, htr678a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc567zy, htr067a, htr068a, htr578a, htr678c])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hc567zy, htr367a, htr368a, htr578a, htr678c])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
              linarith only [hlam, hc567zy, htr068b, htr089a, htr578a, htr678b, htr789a])
            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr068c, htr069b, htr089c])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, hc023xy, hc589zy, htr024a, htr036a, htr245a, htr368a, htr459a, htr689a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              linarith only [hlam, hc026xy, hc5910zy, htr024a, htr068a, htr245a, htr4510a, htr689a, htr8910a])
            obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc026xy, hc589zy, htr024a, htr069a, htr245a, htr459a, htr6910a, htr8910a])
            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc567zy, htr579c, htr5910a, htr679a, htr7910a]
              ·
                linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a]
            ·
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hd23b, hd79a, htr036a, htr037a, htr236a, htr367b, htr679a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              rcases m.htr 3 7 8 (by decide) (by decide) with
                ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
              ·
                linarith only [hlam, hd34a, hd57b, htr034a, htr037a, htr378a, htr578a]
              ·
                linarith only [hlam, hd23b, hd79a, htr237a, htr378a, htr678a, htr679a]
          ·
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc357yz, htr378a, htr578c, htr589a, htr789a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hc578zy, htr378a, htr379a, htr589a, htr789c])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc578zy, htr589a, htr678a, htr679a, htr789c])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                linarith only [hlam, hc578zy, htr379b, htr3910a, htr589a, htr789b, htr8910a])
              obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc023xy, hc5910zy, htr024a, htr037a, htr245a, htr379a, htr4510a, htr7910a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr039a, htr039b, htr039c, _, _⟩
                linarith only [hlam, hd23b, hd910a, htr037a, htr039a, htr237a, htr3910a])
              obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hd23b, hd910a, htr236a, htr367a, htr679a, htr7910a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              rcases m.htr 0 3 6 (by decide) (by decide) with
                ⟨htr036a, htr036b, htr036c, _, _⟩ | ⟨htr036a, htr036b, htr036c, _, _⟩
              ·
                linarith only [hlam, hd26b, hd34a, htr034a, htr036a, htr267a, htr367a]
              ·
                linarith only [hlam, hc236zy, htr036a, htr039a, htr267a, htr367c, htr379c]
            ·
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hd23b, hd89a, htr236a, htr367a, htr678a, htr789a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hd26b, hd34a, htr034a, htr036a, htr267a, htr367a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc236zy, htr036a, htr037a, htr267a, htr367c])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              rcases m.htr 3 7 8 (by decide) (by decide) with
                ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
              ·
                linarith only [hlam, hc236zy, htr267a, htr367b, htr378a, htr678a]
              ·
                linarith only [hlam, hc023xy, hc589zy, htr024a, htr037a, htr245a, htr378a, htr459a, htr789a]
        ·
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, hc027yz, htr0710a, htr1210a, htr127a, htr2710b])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, hc236zy, htr1210a, htr126a, htr2610b, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, hc237zy, htr1210a, htr127a, htr2710b, htr3710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc267zy, htr1210a, htr127a, htr2710b, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc278zy, htr1210a, htr128a, htr2810b, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc279zy, htr1210a, htr129a, htr2910b, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hc027xy, hc5710zy, htr024a, htr078a, htr245a, htr4510a, htr6710a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, hd57b, hd910a, htr078a, htr079a, htr578a, htr7910a])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, hc023xy, hc5710zy, htr024a, htr036a, htr245a, htr367a, htr4510a, htr6710a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd23b, hd710a, htr036a, htr037a, htr236a, htr3710a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            rcases m.htr 3 7 9 (by decide) (by decide) with
              ⟨htr379a, htr379b, htr379c, _, _⟩ | ⟨htr379a, htr379b, htr379c, _, _⟩
            ·
              linarith only [hlam, hd34a, hd57b, htr034a, htr037a, htr379a, htr579a]
            ·
              linarith only [hlam, hd23b, hd710a, htr0710a, htr079a, htr237a, htr379a]
          ·
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hd26b, hd710a, htr0710a, htr078a, htr267a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, hd57b, hd810a, htr078a, htr079a, htr579a, htr7810a])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hd23b, hd810a, htr236a, htr367a, htr678a, htr7810a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, hd26b, hd34a, htr034a, htr036a, htr267a, htr367a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd23b, hd610a, htr036a, htr037a, htr237a, htr3610a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            rcases m.htr 3 7 9 (by decide) (by decide) with
              ⟨htr379a, htr379b, htr379c, _, _⟩ | ⟨htr379a, htr379b, htr379c, _, _⟩
            ·
              linarith only [hlam, hc027xy, hc5710zy, htr024a, htr079a, htr245a, htr3710a, htr379a, htr4510a]
            ·
              linarith only [hlam, hc023xy, hc5910zy, htr024a, htr037a, htr245a, htr379a, htr4510a, htr7910a]
      ·
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc236zy, htr126a, htr129a, htr269b, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc237zy, htr127a, htr129a, htr279b, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc267zy, htr127a, htr129a, htr279b, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc278zy, htr128a, htr129a, htr289b, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hc023xy, hc579zy, htr024a, htr036a, htr245a, htr367a, htr459a, htr679a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd23b, hd79a, htr036a, htr037a, htr236a, htr379a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd57b, htr034a, htr037a, htr378a, htr578a]
          ·
            linarith only [hlam, hd23b, hd79a, htr237a, htr378a, htr678a, htr679a]
        ·
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd23b, hd89a, htr236a, htr367a, htr678a, htr789a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hd26b, hd34a, htr034a, htr036a, htr267a, htr367a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd23b, hd69a, htr036a, htr037a, htr237a, htr369a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          rcases m.htr 3 7 8 (by decide) (by decide) with
            ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
          ·
            linarith only [hlam, hd26b, hd79a, htr267a, htr378a, htr379a, htr678a]
          ·
            linarith only [hlam, hc023xy, hc589zy, htr024a, htr037a, htr245a, htr378a, htr459a, htr789a]
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc023yz, htr038a, htr123a, htr128a, htr238b])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc236zy, htr126a, htr128a, htr268b, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc237zy, htr127a, htr128a, htr278b, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc267zy, htr127a, htr128a, htr278b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr123a, htr128a, htr289a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, hc358yz, htr038a, htr039a, htr239b, htr289c, htr589a])
        obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc568zy, htr269b, htr289c, htr368a, htr369a, htr589a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc578zy, htr378a, htr379a, htr589a, htr789c])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc578zy, htr589a, htr678a, htr679a, htr789c])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a])
        obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hc578zy, htr379b, htr3910a, htr589a, htr789b, htr8910a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd23b, hd910a, htr036a, htr039a, htr236a, htr3910a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc023xy, hc5910zy, htr024a, htr036a, htr245a, htr369a, htr4510a, htr679b, htr7910a]
      ·
        rcases m.htr 3 6 7 (by decide) (by decide) with
          ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
        ·
          linarith only [hlam, hd26b, hd89a, htr267a, htr367a, htr368a, htr678b, htr789a]
        ·
          linarith only [hlam, hd23b, hd89a, htr236a, htr367a, htr678a, htr789a]
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc023yz, htr037a, htr123a, htr127a, htr237b])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc236zy, htr126a, htr127a, htr267b, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd23b, hd67a, htr123a, htr127a, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc357yz, htr037a, htr038a, htr238b, htr278c, htr578a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc567zy, htr367a, htr368a, htr578a, htr678c])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc567zy, htr368b, htr389a, htr578a, htr678b, htr789a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd23b, hd89a, htr036a, htr038a, htr236a, htr389a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a]
      ·
        linarith only [hlam, hc023xy, hc589zy, htr024a, htr036a, htr245a, htr368a, htr459a, htr689a]
    ·
      rcases m.htr 0 3 6 (by decide) (by decide) with
        ⟨htr036a, htr036b, htr036c, _, _⟩ | ⟨htr036a, htr036b, htr036c, _, _⟩
      ·
        linarith only [hlam, hd23b, hd78a, htr036a, htr037a, htr236a, htr367b, htr678a]
      ·
        linarith only [hlam, hc023xy, hc578zy, htr024a, htr036a, htr245a, htr367a, htr458a, htr678a]

theorem shard_052 {lam p : ℝ} (m : ElevenModel lam p)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr239b : m.d 3 9 < m.d 2 9)
    : False :=
  proof_shard_052 m htr024a htr025a htr034a htr123a htr124a htr124b htr124c htr125a htr125b htr125c htr126a htr126b htr236a htr237a htr237b htr238b htr239b

#print axioms shard_052
end Jsp404.NoSatElevenDBMTerminal
