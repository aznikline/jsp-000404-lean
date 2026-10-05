import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_040 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr028c : m.d 0 8 < m.d 2 8)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr246b : m.d 4 6 < m.d 2 6)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr248b : m.d 4 8 < m.d 2 8)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  have hd05a := (m.hrange 0 5 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  have hd37a := (m.hrange 3 7 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
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
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc023yz, htr037a, htr123a, htr127a, htr237b])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc024yz, htr047a, htr124a, htr127a, htr247b])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc234zy, htr124a, htr127a, htr247b, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  rcases m.htr 1 2 8 (by decide) (by decide) with
    ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
  ·
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, htr125c, htr128b, htr158c])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, htr126c, htr128b, htr168c])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, htr127c, htr128b, htr178c])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, htr125b, htr158a, htr258a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hc568xy, htr125a, htr128a, htr256a, htr258c])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, htr126b, htr168a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc678xy, htr126a, htr128a, htr267a, htr268c])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, htr127b, htr178a, htr278a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc256yz, htr126a, htr128a, htr268c, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hd02a, hd68b, htr026a, htr267a, htr567a, htr568a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd02a, hd78b, htr025a, htr256a, htr567a, htr678a]
    ·
      linarith only [hlam, hd02a, hd67b, htr025a, htr125a, htr128a, htr278c, htr678a]
  ·
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc023yz, htr038a, htr123a, htr128a, htr238b])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc024yz, htr048a, htr124a, htr128a, htr248b])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, hc234zy, htr124a, htr128a, htr248b, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    rcases m.htr 1 2 9 (by decide) (by decide) with
      ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
    ·
      have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr159a, htr159b, htr159c, _, _⟩
        linarith only [hlam, htr125c, htr129b, htr159c])
      obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, htr126c, htr129b, htr169c])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, htr127c, htr129b, htr179c])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr259a, htr259b, htr259c, _, _⟩
        linarith only [hlam, htr125b, htr159a, htr259a])
      obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc569xy, htr125a, htr129a, htr256a, htr259c])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, htr126b, htr169a, htr269a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc679xy, htr126a, htr129a, htr267a, htr269c])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, htr127b, htr179a, htr279a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc256yz, htr126a, htr129a, htr269c, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hd02a, hd69b, htr026a, htr267a, htr567a, htr569a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        linarith only [hlam, hd02a, hd79b, htr025a, htr256a, htr567a, htr679a]
      ·
        linarith only [hlam, hd02a, hd67b, htr025a, htr125a, htr129a, htr279c, htr679a]
    ·
      rcases m.htr 1 2 10 (by decide) (by decide) with
        ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
      ·
        have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
          linarith only [hlam, htr1210b, htr125c, htr1510c])
        obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
        have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
          linarith only [hlam, htr1210b, htr126c, htr1610c])
        obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
        have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
          linarith only [hlam, htr1210b, htr127c, htr1710c])
        obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
        have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
          linarith only [hlam, htr125b, htr1510a, htr2510a])
        obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc5610xy, htr1210a, htr125a, htr2510c, htr256a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
          linarith only [hlam, htr126b, htr1610a, htr2610a])
        obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc6710xy, htr1210a, htr126a, htr2610c, htr267a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
          linarith only [hlam, htr127b, htr1710a, htr2710a])
        obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
        have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
          linarith only [hlam, hc256yz, htr1210a, htr126a, htr2610c, htr5610a])
        obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd02a, hd610b, htr026a, htr267a, htr5610a, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        rcases m.htr 6 7 10 (by decide) (by decide) with
          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        ·
          linarith only [hlam, hd02a, hd710b, htr025a, htr256a, htr567a, htr6710a]
        ·
          linarith only [hlam, hd02a, hd67b, htr025a, htr1210a, htr125a, htr2710c, htr6710a]
      ·
        rcases m.htr 0 3 4 (by decide) (by decide) with
          ⟨htr034a, htr034b, htr034c, _, _⟩ | ⟨htr034a, htr034b, htr034c, _, _⟩
        ·
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hd23b, hd56a, htr034a, htr035a, htr234a, htr356a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hd23b, hd35a, htr123a, htr125a, htr256a, htr356a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd23b, hd67a, htr034a, htr036a, htr234a, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hd23b, hd36a, htr123a, htr126a, htr267a, htr367a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, hd23b, hd68a, htr034a, htr036a, htr234a, htr368a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hd23b, hd36a, htr123a, htr126a, htr268a, htr368a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd23b, hd78a, htr034a, htr037a, htr234a, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hd23b, hd37a, htr123a, htr127a, htr278a, htr378a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd23b, hd89a, htr034a, htr038a, htr234a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd02a, hd67b, htr026a, htr268a, htr567a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd02a, hd78b, htr025a, htr256a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hd02a, hd89b, htr025a, htr256a, htr568a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd02a, hd68b, htr027a, htr278a, htr689a, htr789a]
            ·
              linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a]
          ·
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd02a, hd68b, htr026a, htr267a, htr567a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc356yz, htr368b, htr389a, htr568a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd02a, hd89b, htr026a, htr267a, htr678a, htr789a]
            ·
              linarith only [hlam, hd02a, hd78b, htr026a, htr268a, htr689a, htr789a]
        ·
          rcases m.htr 2 5 6 (by decide) (by decide) with
            ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, htr025c, htr056a, htr256a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc235yx, htr123a, htr125c, htr156a, htr256a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, htr245b, htr256a, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            rcases m.htr 2 5 7 (by decide) (by decide) with
              ⟨htr257a, htr257b, htr257c, _, _⟩ | ⟨htr257a, htr257b, htr257c, _, _⟩
            ·
              rcases m.htr 2 6 7 (by decide) (by decide) with
                ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
              ·
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, htr026c, htr067a, htr267a])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc236yx, htr123a, htr126c, htr167a, htr267a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, htr246b, htr267a, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                rcases m.htr 5 6 7 (by decide) (by decide) with
                  ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                ·
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hc023xy, hc678yx, htr025a, htr034a, htr256a, htr346a, htr468a, htr567a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, hd23b, hd46a, htr123a, htr126a, htr268a, htr468a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                    linarith only [hlam, hc023xy, hc679yx, htr025a, htr034a, htr256a, htr346a, htr469a, htr567a])
                  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                    linarith only [hlam, hd23b, hd46a, htr123a, htr126a, htr269a, htr469a])
                  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hd02a, hd67b, htr026a, htr268a, htr567a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc023xy, hc678zy, htr025a, htr034a, htr256a, htr347a, htr478a, htr568a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hd23b, hd47a, htr123a, htr127a, htr278a, htr478a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                    linarith only [hlam, hd02a, hd67b, htr026a, htr269a, htr567a, htr569a])
                  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc023xy, hc689zy, htr025a, htr034a, htr256a, htr348a, htr489a, htr569a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd02a, hd78b, htr025a, htr256a, htr567a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd02a, hd89b, htr025a, htr256a, htr568a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd02a, hd68b, htr027a, htr278a, htr689a, htr789a]
                  ·
                    linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a]
                ·
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, hc568yx, htr156b, htr158a, htr167a, htr567a])
                  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hd02a, hd68b, htr026a, htr267a, htr567a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  rcases m.htr 4 6 8 (by decide) (by decide) with
                    ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                  ·
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, hc456yz, htr026c, htr068a, htr267a, htr468a, htr567a])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc456yz, htr167a, htr168a, htr468a, htr567a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    rcases m.htr 4 6 9 (by decide) (by decide) with
                      ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                    ·
                      rcases m.htr 4 6 10 (by decide) (by decide) with
                        ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                      ·
                        rcases m.htr 6 7 8 (by decide) (by decide) with
                          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                        ·
                          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                            linarith only [hlam, hc023xy, hc789yx, htr026a, htr034a, htr267a, htr347a, htr479a, htr678a])
                          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                            linarith only [hlam, hc456yz, htr167c, htr179a, htr467b, htr479a, htr567a])
                          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hd02a, hd57b, htr026a, htr267a, htr578a, htr678a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                            linarith only [hlam, hd01a, hd78b, htr017a, htr179a, htr578a, htr579a])
                          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                            linarith only [hlam, hc023xy, hc789zy, htr025a, htr034a, htr257a, htr348a, htr489a, htr579a])
                          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                            linarith only [hlam, hc456yz, htr468b, htr489a, htr568a, htr689a])
                          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd02a, hd89b, htr026a, htr267a, htr678a, htr789a]
                          ·
                            linarith only [hlam, hd01a, hd78b, htr016a, htr168a, htr689a, htr789a]
                        ·
                          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                            linarith only [hlam, hc056yz, htr067b, htr078a, htr567a, htr678a])
                          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                            linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
                          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hc023xy, hc789xy, htr026a, htr034a, htr267a, htr347a, htr478a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                            linarith only [hlam, hc056yz, htr067b, htr079a, htr567a, htr679a])
                          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                            linarith only [hlam, hd23b, hd78a, htr027c, htr079a, htr123a, htr127a, htr478a, htr479a])
                          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc013xy, hc789yz, htr015a, htr034a, htr158a, htr347a, htr479a, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                            linarith only [hlam, hc013xy, hc578zy, htr018a, htr034a, htr189a, htr347a, htr478a, htr589a])
                          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                            linarith only [hlam, hc456yz, htr048b, htr089a, htr168c, htr189a, htr468b, htr568a])
                          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd23b, hd78a, htr028c, htr089a, htr123a, htr128a, htr789a]
                          ·
                            linarith only [hlam, hd23b, hd89a, htr027c, htr078a, htr123a, htr127a, htr789a]
                      ·
                        have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                          linarith only [hlam, htr046b, htr0610a, htr4610a])
                        obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                          linarith only [hlam, htr0610c, htr067b, htr0710b])
                        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, htr0610c, htr068b, htr0810b])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                          linarith only [hlam, hd23b, hd610a, htr027c, htr0710a, htr123a, htr127a, htr4610a, htr467b, htr4710a])
                        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hc023xy, hc7810yx, htr026a, htr034a, htr267a, htr347a, htr4710a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                          linarith only [hlam, hc056yz, htr067b, htr078a, htr567a, htr678a])
                        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                        rcases m.htr 7 8 10 (by decide) (by decide) with
                          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                        ·
                          linarith only [hlam, hd23b, hd78a, htr028c, htr0810a, htr123a, htr128a, htr7810a]
                        ·
                          linarith only [hlam, hd23b, hd810a, htr027c, htr078a, htr123a, htr127a, htr7810a]
                    ·
                      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                        linarith only [hlam, htr046b, htr069a, htr469a])
                      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, htr067b, htr069c, htr079b])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, htr068b, htr069c, htr089b])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hd23b, hd69a, htr027c, htr079a, htr123a, htr127a, htr467b, htr469a, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc023xy, hc789yx, htr026a, htr034a, htr267a, htr347a, htr479a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, hc056yz, htr067b, htr078a, htr567a, htr678a])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd23b, hd78a, htr028c, htr089a, htr123a, htr128a, htr789a]
                      ·
                        linarith only [hlam, hd23b, hd89a, htr027c, htr078a, htr123a, htr127a, htr789a]
                  ·
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, htr046b, htr068a, htr468a])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, htr067b, htr068c, htr078b])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, htr146b, htr168a, htr468a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hd23b, hd68a, htr027c, htr078a, htr123a, htr127a, htr467b, htr468a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hc023xy, hc789xy, htr026a, htr034a, htr267a, htr347a, htr478a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, hc056yz, htr067b, htr079a, htr567a, htr679a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hd23b, hd68a, htr027c, htr079a, htr123a, htr127a, htr467b, htr468a, htr479a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hc013xy, hc789yz, htr015a, htr034a, htr158a, htr347a, htr479a, htr589a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc013xy, hc568zy, htr018a, htr034a, htr189a, htr346a, htr468a, htr589a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd56b, hd78a, htr167a, htr168c, htr189a, htr567a, htr789a]
                    ·
                      linarith only [hlam, hd23b, hd89a, htr027c, htr078a, htr123a, htr127a, htr789a]
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, htr126b, htr167a, htr267a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hd23b, hd46a, htr123a, htr126a, htr267a, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd23b, hd78a, htr123a, htr126a, htr267a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hd23b, hd67a, htr123a, htr127a, htr278a, htr678a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc023xy, hc567zy, htr027a, htr034a, htr278a, htr346a, htr467a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc023xy, hc678yz, htr025a, htr034a, htr257a, htr346a, htr468a, htr578a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hd23b, hd67a, htr123a, htr126c, htr168a, htr467a, htr468a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc023xy, hc789yx, htr025a, htr034a, htr257a, htr347a, htr479a, htr578a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc678xy, htr167c, htr168a, htr179a, htr467b, htr479a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc013xy, hc567zy, htr017a, htr034a, htr179a, htr346a, htr467a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc023xy, hc789zy, htr025a, htr034a, htr257a, htr348a, htr489a, htr579a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc678xy, htr467a, htr468b, htr489a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd02a, hd89b, htr025a, htr257a, htr578a, htr789a]
                ·
                  linarith only [hlam, hd67a, hd78b, htr467a, htr468a, htr689a, htr789a]
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hd05a, hd23b, htr057a, htr123a, htr125a, htr257a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, htr056b, htr057c, htr067b])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, htr125b, htr157a, htr257a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                linarith only [hlam, hd23b, hd45a, htr123a, htr125a, htr257a, htr457a])
              obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd23b, hd57a, htr026c, htr067a, htr123a, htr126a, htr456b, htr457a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc023xy, hc678xy, htr025a, htr034a, htr256a, htr346a, htr467a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd23b, hd57a, htr026c, htr068a, htr123a, htr126a, htr456b, htr457a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                linarith only [hlam, hc023xy, hc679xy, htr025a, htr034a, htr256a, htr346a, htr467a, htr569a])
              obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc567yx, htr056b, htr057a, htr069a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hd23b, hd57a, htr026c, htr069a, htr123a, htr126a, htr456b, htr457a, htr469a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd23b, hd78a, htr123a, htr125a, htr257a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc567yx, htr156a, htr157c, htr178a, htr578a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd23b, hd89a, htr026c, htr068a, htr123a, htr126a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hd23b, hd68a, htr123a, htr128a, htr289a, htr689a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc013xy, hc689yz, htr017a, htr034a, htr178a, htr346a, htr469a, htr789a]
              ·
                linarith only [hlam, hc023xy, hc678yz, htr028a, htr034a, htr289a, htr346a, htr468a, htr789a]
          ·
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hd23b, hd45a, htr123a, htr125a, htr256a, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd23b, hd67a, htr123a, htr125a, htr256a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr267a, htr567a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd23b, hd68a, htr123a, htr125a, htr256a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hd23b, hd56a, htr123a, htr126a, htr268a, htr568a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            rcases m.htr 4 5 7 (by decide) (by decide) with
              ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hd23b, hd56a, htr025c, htr057a, htr123a, htr125a, htr456a, htr457a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hd23b, hd56a, htr123a, htr125c, htr157a, htr456a, htr457a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              rcases m.htr 4 5 8 (by decide) (by decide) with
                ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
              ·
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hd23b, hd56a, htr025c, htr058a, htr123a, htr125a, htr456a, htr458a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, hc567xy, htr157a, htr158a, htr456a, htr458a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                rcases m.htr 4 5 9 (by decide) (by decide) with
                  ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
                ·
                  rcases m.htr 4 5 10 (by decide) (by decide) with
                    ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                  ·
                    rcases m.htr 4 7 8 (by decide) (by decide) with
                      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                    ·
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hc013xy, hc789yx, htr015a, htr034a, htr157a, htr347a, htr479a, htr578a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc567xy, htr456a, htr457b, htr479a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc013xy, hc789zy, htr015a, htr034a, htr157a, htr348a, htr489a, htr579a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc568xy, htr456a, htr458b, htr489a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd56a, hd89b, htr456a, htr457a, htr578a, htr789a]
                      ·
                        linarith only [hlam, hd56a, hd78b, htr456a, htr458a, htr589a, htr789a]
                    ·
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc013xy, hc789xy, htr015a, htr034a, htr157a, htr347a, htr478a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, hc567xy, htr047b, htr079a, htr456a, htr457b, htr579a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hd23b, hd56a, htr027c, htr079a, htr123a, htr127a, htr456a, htr457b, htr479a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc013xy, hc789yz, htr015a, htr034a, htr158a, htr347a, htr479a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, hc568xy, htr048b, htr089a, htr456a, htr458b, htr589a])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd23b, hd78a, htr028c, htr089a, htr123a, htr128a, htr789a]
                      ·
                        linarith only [hlam, hd23b, hd89a, htr123a, htr127a, htr247b, htr478a, htr789a]
                  ·
                    have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                      linarith only [hlam, htr045b, htr0510a, htr4510a])
                    obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                    have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                      linarith only [hlam, htr0510c, htr057b, htr0710b])
                    obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, htr0510c, htr058b, htr0810b])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                      linarith only [hlam, hd23b, hd56a, htr027c, htr0710a, htr123a, htr127a, htr456a, htr457b, htr4710a])
                    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hc013xy, hc7810yx, htr015a, htr034a, htr157a, htr347a, htr4710a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hc567xy, htr047b, htr078a, htr456a, htr457b, htr578a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    rcases m.htr 7 8 10 (by decide) (by decide) with
                      ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    ·
                      linarith only [hlam, hd23b, hd78a, htr028c, htr0810a, htr123a, htr128a, htr7810a]
                    ·
                      linarith only [hlam, hd23b, hd810a, htr027c, htr078a, htr123a, htr127a, htr7810a]
                ·
                  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                    linarith only [hlam, htr045b, htr059a, htr459a])
                  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, htr057b, htr059c, htr079b])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, htr058b, htr059c, htr089b])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hd23b, hd56a, htr027c, htr079a, htr123a, htr127a, htr456a, htr457b, htr479a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc013xy, hc789yx, htr015a, htr034a, htr157a, htr347a, htr479a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, hc567xy, htr047b, htr078a, htr456a, htr457b, htr578a])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd23b, hd78a, htr028c, htr089a, htr123a, htr128a, htr789a]
                  ·
                    linarith only [hlam, hd23b, hd89a, htr027c, htr078a, htr123a, htr127a, htr789a]
              ·
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, htr045b, htr058a, htr458a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr057b, htr058c, htr078b])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, htr145b, htr158a, htr458a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd23b, hd56a, htr027c, htr078a, htr123a, htr127a, htr456a, htr457b, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc013xy, hc789xy, htr015a, htr034a, htr157a, htr347a, htr478a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hc567xy, htr047b, htr079a, htr456a, htr457b, htr579a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hd23b, hd56a, htr027c, htr079a, htr123a, htr127a, htr456a, htr457b, htr479a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd23b, hd89a, htr123a, htr125a, htr245b, htr458a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc578yx, htr157a, htr158c, htr189a, htr589a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                rcases m.htr 6 8 9 (by decide) (by decide) with
                  ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                ·
                  linarith only [hlam, hc023xy, hc789yz, htr026a, htr034a, htr268a, htr347a, htr479a, htr689a]
                ·
                  linarith only [hlam, hc013xy, hc568yz, htr018a, htr034a, htr189a, htr345a, htr458a, htr689a]
            ·
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd23b, hd78a, htr123a, htr125a, htr245b, htr457a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hd23b, hd57a, htr123a, htr127a, htr278a, htr578a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd23b, hd79a, htr123a, htr125a, htr245b, htr457a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hd23b, hd57a, htr123a, htr127a, htr279a, htr579a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc023xy, hc567yz, htr027a, htr034a, htr278a, htr345a, htr457a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                linarith only [hlam, hc023xy, hc578yz, htr026a, htr034a, htr267a, htr345a, htr458a, htr678a])
              obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc023xy, hc567yz, htr027a, htr034a, htr279a, htr345a, htr457a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc023xy, hc789zy, htr026a, htr034a, htr267a, htr348a, htr489a, htr679a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568xy, htr456a, htr458b, htr489a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd02a, hd89b, htr026a, htr267a, htr678a, htr789a]
              ·
                linarith only [hlam, hd56a, hd78b, htr456a, htr458a, htr589a, htr789a]

theorem shard_040 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr028c : m.d 0 8 < m.d 2 8)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr246b : m.d 4 6 < m.d 2 6)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr248b : m.d 4 8 < m.d 2 8)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_040 m htr015a htr016a htr017a htr018a htr025a htr025c htr026a htr026c htr027a htr027c htr028a htr028c htr035a htr036a htr045b htr046b htr123a htr124a htr125a htr125b htr125c htr126a htr126b htr126c htr127a htr127b htr127c htr145b htr146b htr234a htr237b htr238b htr245b htr246b htr247b htr248b htr345a htr346a

#print axioms shard_040
end Jsp404.NoSatElevenDBMTerminal
