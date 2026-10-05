import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_068 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr248b : m.d 4 8 < m.d 2 8)
    (htr249b : m.d 4 9 < m.d 2 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < 4*lam := by
    linarith only [hd26braw, hp]
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
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
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc279xy, hc279yx, hc279yz, hc279zy⟩ := endpoint_caps m 2 7 9 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc5710xy, hc5710yx, hc5710yz, hc5710zy⟩ := endpoint_caps m 5 7 10 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr125c, htr126b, htr156c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
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
    linarith only [hlam, hd02a, hd67b, htr023a, htr123a, htr126a, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd02a, hd68b, htr023a, htr123a, htr126a, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd02a, hd69b, htr023a, htr123a, htr126a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hd02a, hd610b, htr023a, htr123a, htr126a, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hd02a, hd35b, htr023a, htr123a, htr126a, htr256c, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hd02a, hd56b, htr023a, htr235b, htr257a, htr356a, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hd02a, hd56b, htr023a, htr235b, htr258a, htr356a, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hd02a, hd56b, htr023a, htr235b, htr259a, htr356a, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, hd02a, hd56b, htr023a, htr235b, htr2510a, htr3510a, htr356a])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, htr256c, htr267a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd01a, hd78b, htr013a, htr135a, htr357a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hd01a, hd79b, htr013a, htr135a, htr357a, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
    linarith only [hlam, hd01a, hd710b, htr013a, htr135a, htr357a, htr5710a])
  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
    linarith only [hlam, hd01a, hd89b, htr013a, htr135a, htr358a, htr589a])
  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
    linarith only [hlam, hd01a, hd810b, htr013a, htr135a, htr358a, htr5810a])
  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
    linarith only [hlam, hd01a, hd910b, htr013a, htr135a, htr359a, htr5910a])
  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
  rcases m.htr 1 2 7 (by decide) (by decide) with
    ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
  ·
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd02a, hd57b, htr023a, htr123a, htr127b, htr178a, htr578a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd02a, hd57b, htr023a, htr123a, htr127b, htr179a, htr579a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
      linarith only [hlam, hd02a, hd57b, htr023a, htr123a, htr127b, htr1710a, htr5710a])
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
        linarith only [hlam, hd02a, hd58b, htr023a, htr123a, htr128b, htr189a, htr589a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hd02a, hd58b, htr023a, htr123a, htr128b, htr1810a, htr5810a])
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
          linarith only [hlam, hd02a, hd59b, htr023a, htr123a, htr129b, htr1910a, htr5910a])
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
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc567zy, htr467a, htr468a, htr578a, htr678c])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
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
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc014xy, hc589zy, htr013a, htr046a, htr135a, htr359a, htr468a, htr689a])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              linarith only [hlam, hc016xy, hc5910zy, htr013a, htr068a, htr135a, htr3510a, htr689a, htr8910a])
            obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc016xy, hc589zy, htr013a, htr069a, htr135a, htr359a, htr6910a, htr8910a])
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
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hd24b, hd79a, htr046a, htr047a, htr246a, htr467b, htr679a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                linarith only [hlam, hd45a, hd57b, htr045a, htr047a, htr478a, htr578a]
              ·
                linarith only [hlam, hd24b, hd79a, htr247a, htr478a, htr678a, htr679a]
          ·
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc457yz, htr478a, htr578c, htr589a, htr789a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc578zy, htr478a, htr479a, htr589a, htr789c])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc578zy, htr589a, htr678a, htr679a, htr789c])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc578zy, htr479b, htr4910a, htr589a, htr789b, htr8910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc014xy, hc5910zy, htr013a, htr047a, htr135a, htr3510a, htr479a, htr7910a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr049a, htr049b, htr049c, _, _⟩
                linarith only [hlam, hd24b, hd910a, htr047a, htr049a, htr247a, htr4910a])
              obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd24b, hd910a, htr246a, htr467a, htr679a, htr7910a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              rcases m.htr 0 4 6 (by decide) (by decide) with
                ⟨htr046a, htr046b, htr046c, _, _⟩ | ⟨htr046a, htr046b, htr046c, _, _⟩
              ·
                linarith only [hlam, hc024yz, htr046a, htr246c, htr267a, htr467a]
              ·
                linarith only [hlam, hc246zy, htr046a, htr049a, htr267a, htr467c, htr479c]
            ·
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd24b, hd89a, htr246a, htr467a, htr678a, htr789a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                linarith only [hlam, hc024yz, htr046a, htr246c, htr267a, htr467a])
              obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc246zy, htr046a, htr047a, htr267a, htr467c])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                linarith only [hlam, hc246zy, htr267a, htr467b, htr478a, htr678a]
              ·
                linarith only [hlam, hc014xy, hc589zy, htr013a, htr047a, htr135a, htr359a, htr478a, htr789a]
        ·
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, hc027yz, htr0710a, htr1210a, htr127a, htr2710b])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, hc246zy, htr1210a, htr126a, htr2610b, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, hc247zy, htr1210a, htr127a, htr2710b, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
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
              linarith only [hlam, hc017xy, hc5710zy, htr013a, htr078a, htr135a, htr3510a, htr6710a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, hd57b, hd910a, htr078a, htr079a, htr578a, htr7910a])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc014xy, hc5710zy, htr013a, htr046a, htr135a, htr3510a, htr467a, htr6710a])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hd24b, hd710a, htr046a, htr047a, htr246a, htr4710a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            rcases m.htr 4 7 9 (by decide) (by decide) with
              ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
            ·
              linarith only [hlam, hd45a, hd57b, htr045a, htr047a, htr479a, htr579a]
            ·
              linarith only [hlam, hd24b, hd710a, htr0710a, htr079a, htr247a, htr479a]
          ·
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, hd26b, hd710a, htr0710a, htr078a, htr267a, htr678a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, hd57b, hd810a, htr078a, htr079a, htr579a, htr7810a])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd24b, hd810a, htr246a, htr467a, htr678a, htr7810a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc024yz, htr046a, htr246c, htr267a, htr467a])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr047a, htr047b, htr047c, _, _⟩
              linarith only [hlam, hd24b, hd610a, htr046a, htr047a, htr247a, htr4610a])
            obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
            rcases m.htr 4 7 9 (by decide) (by decide) with
              ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
            ·
              linarith only [hlam, hc017xy, hc5710zy, htr013a, htr079a, htr135a, htr3510a, htr4710a, htr479a]
            ·
              linarith only [hlam, hc014xy, hc5910zy, htr013a, htr047a, htr135a, htr3510a, htr479a, htr7910a]
      ·
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc246zy, htr126a, htr129a, htr269b, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc247zy, htr127a, htr129a, htr279b, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
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
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc014xy, hc579zy, htr013a, htr046a, htr135a, htr359a, htr467a, htr679a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd24b, hd79a, htr046a, htr047a, htr246a, htr479a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hd45a, hd57b, htr045a, htr047a, htr478a, htr578a]
          ·
            linarith only [hlam, hd24b, hd79a, htr247a, htr478a, htr678a, htr679a]
        ·
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd24b, hd89a, htr246a, htr467a, htr678a, htr789a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, hc024yz, htr046a, htr246c, htr267a, htr467a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hd24b, hd69a, htr046a, htr047a, htr247a, htr469a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hd26b, hd79a, htr267a, htr478a, htr479a, htr678a]
          ·
            linarith only [hlam, hc014xy, hc589zy, htr013a, htr047a, htr135a, htr359a, htr478a, htr789a]
    ·
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc024yz, htr048a, htr124a, htr128a, htr248b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc246zy, htr126a, htr128a, htr268b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc247zy, htr127a, htr128a, htr278b, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc267zy, htr127a, htr128a, htr278b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd24b, hd78a, htr124a, htr128a, htr289a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr049a, htr049b, htr049c, _, _⟩
          linarith only [hlam, hc458yz, htr048a, htr049a, htr249b, htr289c, htr589a])
        obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc568zy, htr269b, htr289c, htr468a, htr469a, htr589a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc578zy, htr478a, htr479a, htr589a, htr789c])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc578zy, htr589a, htr678a, htr679a, htr789c])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a])
        obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc578zy, htr479b, htr4910a, htr589a, htr789b, htr8910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hd24b, hd910a, htr046a, htr049a, htr246a, htr4910a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc014xy, hc5910zy, htr013a, htr046a, htr135a, htr3510a, htr469a, htr679b, htr7910a]
      ·
        rcases m.htr 4 6 7 (by decide) (by decide) with
          ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
        ·
          linarith only [hlam, hd26b, hd89a, htr267a, htr467a, htr468a, htr678b, htr789a]
        ·
          linarith only [hlam, hd24b, hd89a, htr246a, htr467a, htr678a, htr789a]
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc024yz, htr047a, htr124a, htr127a, htr247b])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc246zy, htr126a, htr127a, htr267b, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd24b, hd67a, htr124a, htr127a, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc457yz, htr047a, htr048a, htr248b, htr278c, htr578a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc567zy, htr467a, htr468a, htr578a, htr678c])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc567zy, htr468b, htr489a, htr578a, htr678b, htr789a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hd24b, hd89a, htr046a, htr048a, htr246a, htr489a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a]
      ·
        linarith only [hlam, hc014xy, hc589zy, htr013a, htr046a, htr135a, htr359a, htr468a, htr689a]
    ·
      rcases m.htr 0 4 6 (by decide) (by decide) with
        ⟨htr046a, htr046b, htr046c, _, _⟩ | ⟨htr046a, htr046b, htr046c, _, _⟩
      ·
        linarith only [hlam, hd24b, hd78a, htr046a, htr047a, htr246a, htr467b, htr678a]
      ·
        linarith only [hlam, hc014xy, hc578zy, htr013a, htr046a, htr135a, htr358a, htr467a, htr678a]

theorem shard_068 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr248b : m.d 4 8 < m.d 2 8)
    (htr249b : m.d 4 9 < m.d 2 9)
    : False :=
  proof_shard_068 m htr013a htr023a htr045a htr123a htr124a htr125a htr125b htr125c htr126a htr126b htr135a htr235b htr246a htr246c htr247a htr247b htr248b htr249b

#print axioms shard_068
end Jsp404.NoSatElevenDBMTerminal
