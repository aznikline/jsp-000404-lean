import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_584 {lam p : ℝ} (m : ElevenModel lam p)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr249c : m.d 2 9 < m.d 4 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd27a := (m.hrange 2 7 (by decide)).1
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
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
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc289xy, hc289yx, hc289yz, hc289zy⟩ := endpoint_caps m 2 8 9 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, htr125b, htr127c, htr157b])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, htr126b, htr127c, htr167b])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, htr125c, htr157a, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc567yx, htr125a, htr127a, htr256a, htr257b])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, htr126c, htr167a, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hc678xy, htr126a, htr127a, htr267b, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hc679xy, htr126a, htr127a, htr267b, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hc6710xy, htr126a, htr127a, htr2610a, htr267b])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hd02b, hd78a, htr025a, htr125a, htr127a, htr278a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, hd02b, hd79a, htr025a, htr125a, htr127a, htr279a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
    linarith only [hlam, hd02b, hd710a, htr025a, htr125a, htr127a, htr2710a])
  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hc256zy, htr126a, htr127a, htr267b, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd02b, hd67a, htr026a, htr268a, htr567a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hd02b, hd67a, htr026a, htr269a, htr567a, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hd02b, hd67a, htr026a, htr2610a, htr5610a, htr567a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, htr267b, htr278a, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, htr267b, htr279a, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
    linarith only [hlam, hd02b, hd89a, htr025a, htr256a, htr568a, htr689a])
  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
    linarith only [hlam, hd02b, hd810a, htr025a, htr256a, htr568a, htr6810a])
  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
    linarith only [hlam, hd02b, hd910a, htr025a, htr256a, htr569a, htr6910a])
  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
  rcases m.htr 1 2 8 (by decide) (by decide) with
    ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
  ·
    have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr038a, htr038b, htr038c, _, _⟩
      linarith only [hlam, hc023zy, htr038a, htr123a, htr128a, htr238c])
    obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, hc234yz, htr124a, htr128a, htr248c, htr348a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc237yz, htr127a, htr128a, htr278c, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hc247yz, htr127a, htr128a, htr278c, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      rcases m.htr 3 4 7 (by decide) (by decide) with
        ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
      ·
        linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
      ·
        linarith only [hlam, hd24a, hd89b, htr247a, htr347a, htr348a, htr478c, htr789a]
    ·
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hd23a, hd78b, htr123a, htr128a, htr289a, htr789a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr039a, htr039b, htr039c, _, _⟩
        linarith only [hlam, hc368zy, htr038a, htr039a, htr239c, htr289b, htr689a])
      obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc468zy, htr249c, htr289b, htr348a, htr349a, htr689a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hc678yz, htr378a, htr379a, htr689a, htr789b])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc678yz, htr478a, htr479a, htr689a, htr789b])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a])
      obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
      have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
        linarith only [hlam, hc678yz, htr379c, htr3910a, htr689a, htr789c, htr8910a])
      obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hd23a, hd910b, htr034a, htr039a, htr234a, htr3910a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      rcases m.htr 7 9 10 (by decide) (by decide) with
        ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      ·
        linarith only [hlam, hc023yx, hc6910yz, htr025a, htr034a, htr256a, htr349a, htr479c, htr5610a, htr7910a]
      ·
        linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
  ·
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hd02b, hd68a, htr025a, htr125a, htr128c, htr189a, htr689a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
      linarith only [hlam, hd02b, hd68a, htr025a, htr125a, htr128c, htr1810a, htr6810a])
    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, htr128b, htr189a, htr289a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
      linarith only [hlam, htr128b, htr1810a, htr2810a])
    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
    rcases m.htr 1 2 9 (by decide) (by decide) with
      ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
    ·
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hc237yz, htr127a, htr129a, htr279c, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc247yz, htr127a, htr129a, htr279c, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc278yz, htr128a, htr129a, htr289c, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        rcases m.htr 4 7 8 (by decide) (by decide) with
          ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
        ·
          linarith only [hlam, hd24a, hd910b, htr247a, htr478a, htr789a, htr8910a]
        ·
          linarith only [hlam, hd27a, hd910b, htr278a, htr478a, htr479a, htr789c, htr8910a]
      ·
        rcases m.htr 3 4 7 (by decide) (by decide) with
          ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
        ·
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hc023yx, hc679yz, htr025a, htr034a, htr256a, htr347a, htr479a, htr569a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd23a, hd79b, htr034a, htr037a, htr234a, htr379a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd27a, hd35b, htr035a, htr037a, htr278a, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
          ·
            linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr478a, htr479a]
        ·
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hd24a, hd35b, htr034a, htr035a, htr247a, htr347a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd23a, hd45b, htr034a, htr037a, htr237a, htr345a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc023yx, hc689yz, htr025a, htr037a, htr256a, htr378a, htr569a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hd24a, hd79b, htr247a, htr378a, htr379a, htr478a]
          ·
            linarith only [hlam, hc234yz, htr247b, htr278a, htr347a, htr478a]
    ·
      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
        linarith only [hlam, hd02b, hd69a, htr025a, htr125a, htr129c, htr1910a, htr6910a])
      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
      have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
        linarith only [hlam, htr129b, htr1910a, htr2910a])
      obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
      rcases m.htr 1 2 10 (by decide) (by decide) with
        ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
      ·
        have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
          linarith only [hlam, hc237yz, htr1210a, htr127a, htr2710c, htr3710a])
        obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hc238yz, htr1210a, htr128a, htr2810c, htr3810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc278yz, htr1210a, htr128a, htr2810c, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          linarith only [hlam, hc289yz, htr1210a, htr129a, htr2910c, htr8910a])
        obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr237a, htr378a, htr789a, htr8910a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hd27a, hd35b, htr035a, htr037a, htr278a, htr378a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hd23a, hd710b, htr037a, htr038a, htr238a, htr3710a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          rcases m.htr 3 8 9 (by decide) (by decide) with
            ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
          ·
            linarith only [hlam, hc023yx, hc6910yz, htr025a, htr038a, htr256a, htr389a, htr5610a, htr8910a]
          ·
            linarith only [hlam, hd27a, hd810b, htr278a, htr3810a, htr389a, htr789a]
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc023yx, hc6810yz, htr025a, htr037a, htr256a, htr378a, htr5610a, htr7810a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hd23a, hd810b, htr037a, htr038a, htr237a, htr3810a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          rcases m.htr 3 8 9 (by decide) (by decide) with
            ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd810b, htr238a, htr389a, htr7810a, htr789a]
          ·
            linarith only [hlam, hd35b, hd68a, htr035a, htr038a, htr389a, htr689a]
      ·
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd23a, hd910b, htr237a, htr378a, htr789a, htr8910a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd27a, hd35b, htr035a, htr037a, htr278a, htr378a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, hc237yz, htr037a, htr038a, htr278a, htr378b])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            rcases m.htr 3 8 9 (by decide) (by decide) with
              ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
            ·
              linarith only [hlam, hc023yx, hc6910yz, htr025a, htr038a, htr256a, htr389a, htr5610a, htr8910a]
            ·
              linarith only [hlam, hc237yz, htr278a, htr378c, htr389a, htr789a]
          ·
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hc368zy, htr389a, htr689b, htr6910a, htr8910a])
            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
            rcases m.htr 7 9 10 (by decide) (by decide) with
              ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            ·
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc027yx, hc689yz, htr025a, htr078a, htr256a, htr569a, htr789b, htr7910a, htr8910a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, hd27a, hd89b, htr0710a, htr078a, htr278a, htr7910c, htr8910a])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hd23a, hd89b, htr237a, htr378a, htr789b, htr7910a, htr8910a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hd27a, hd35b, htr035a, htr037a, htr278a, htr378a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hc237yz, htr037a, htr038a, htr278a, htr378b])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, htr037c, htr0710a, htr379a, htr7910b])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              rcases m.htr 3 9 10 (by decide) (by decide) with
                ⟨htr3910a, htr3910b, htr3910c, _, _⟩ | ⟨htr3910a, htr3910b, htr3910c, _, _⟩
              ·
                linarith only [hlam, hc023yx, hc689yz, htr025a, htr038a, htr256a, htr389b, htr3910a, htr569a, htr8910a]
              ·
                linarith only [hlam, hc237yz, htr279a, htr379c, htr3910a, htr7910a]
            ·
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc467zy, htr479a, htr679b, htr6910a, htr7910a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              rcases m.htr 3 4 7 (by decide) (by decide) with
                ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
              ·
                have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr034a, htr034b, htr034c, _, _⟩
                  linarith only [hlam, hc023yx, hc679yz, htr025a, htr034a, htr256a, htr347a, htr479a, htr569a])
                obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
                have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                  linarith only [hlam, hd23a, hd79b, htr034a, htr037a, htr234a, htr379a])
                obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd27a, hd35b, htr035a, htr037a, htr278a, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                rcases m.htr 4 7 8 (by decide) (by decide) with
                  ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                ·
                  linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
                ·
                  linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr478a, htr479a]
              ·
                have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr034a, htr034b, htr034c, _, _⟩
                  linarith only [hlam, hd24a, hd35b, htr034a, htr035a, htr247a, htr347a])
                obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
                have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                  linarith only [hlam, hd23a, hd45b, htr034a, htr037a, htr237a, htr345a])
                obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc023yx, hc689yz, htr025a, htr037a, htr256a, htr378a, htr569a, htr789a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                rcases m.htr 4 7 8 (by decide) (by decide) with
                  ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                ·
                  linarith only [hlam, hd24a, hd79b, htr247a, htr378a, htr379a, htr478a]
                ·
                  linarith only [hlam, hc234yz, htr247b, htr278a, htr347a, htr478a]
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc678yz, htr378a, htr379a, htr689a, htr789b])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc678yz, htr478a, htr479a, htr689a, htr789b])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a])
          obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc023yx, hc6910yz, htr025a, htr037a, htr256a, htr379a, htr5610a, htr7910a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hd23a, hd45b, htr034a, htr037a, htr237a, htr345a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          rcases m.htr 3 4 7 (by decide) (by decide) with
            ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd910b, htr234a, htr347a, htr479a, htr7910a]
          ·
            linarith only [hlam, hd24a, hd35b, htr034a, htr035a, htr247a, htr347a]

theorem shard_584 {lam p : ℝ} (m : ElevenModel lam p)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr249c : m.d 2 9 < m.d 4 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_584 m htr025a htr026a htr035a htr123a htr124a htr125a htr125b htr125c htr126a htr126b htr126c htr127a htr127c htr234a htr237a htr238a htr238c htr239c htr247a htr247b htr248c htr249c htr345a

#print axioms shard_584
end Jsp404.NoSatElevenDBMTerminal
