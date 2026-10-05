import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_581 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr147a : m.d 4 7 + lam ≤ m.d 1 4)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr248c : m.d 2 8 < m.d 2 4)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr258a : m.d 2 5 + lam ≤ m.d 5 8)
    (htr258c : m.d 2 8 < m.d 5 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd25a := (m.hrange 2 5 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  have hd27a := (m.hrange 2 7 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
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
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc289xy, hc289yx, hc289yz, hc289zy⟩ := endpoint_caps m 2 8 9 (by decide) (by decide)
  obtain ⟨hc2910xy, hc2910yx, hc2910yz, hc2910zy⟩ := endpoint_caps m 2 9 10 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd02b, hd67a, htr024a, htr124a, htr126a, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd02b, hd68a, htr024a, htr124a, htr126a, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd02b, hd69a, htr024a, htr124a, htr126a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hd02b, hd610a, htr024a, htr124a, htr126a, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  rcases m.htr 1 2 7 (by decide) (by decide) with
    ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc023zy, htr037a, htr123a, htr127a, htr237c])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc025zy, htr057a, htr125a, htr127a, htr257c])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc235yz, htr125a, htr127a, htr257c, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc236yz, htr126a, htr127a, htr267c, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hc256yz, htr126a, htr127a, htr267c, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    rcases m.htr 3 5 6 (by decide) (by decide) with
      ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
    ·
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hd25a, hd67b, htr258a, htr356a, htr358a, htr567a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd23a, hd78b, htr235a, htr356a, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd23a, hd79b, htr235a, htr356a, htr567a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr027b, htr079a, htr123a, htr127a, htr679a])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr279a, htr679a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, htr037c, htr079a, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr235a, htr356a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd02b, hd78a, htr024a, htr247c, htr279a, htr478a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc678zy, htr568a, htr569a, htr689b, htr789a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr235a, htr356a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd01b, hd910a, htr014a, htr147a, htr479a, htr7910a])
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
            linarith only [hlam, hd01b, hd89a, htr014a, htr147a, htr478a, htr789a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hc023yx, hc467yz, htr024a, htr035a, htr247c, htr278a, htr356a, htr478a, htr567a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd02b, hd79a, htr024a, htr247c, htr278a, htr478a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr039a, htr039b, htr039c, _, _⟩
            linarith only [hlam, hc347zy, htr037a, htr039a, htr239c, htr279b, htr479a])
          obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr035a, htr039a, htr235a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc347zy, htr379c, htr3910a, htr479a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd02b, hd89a, htr024a, htr247c, htr279a, htr7910a, htr8910a]
          ·
            linarith only [hlam, hd02b, hd910a, htr024a, htr247c, htr278a, htr789a, htr8910a]
      ·
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc256yz, htr126a, htr128a, htr268c, htr568a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd02b, hd89a, htr024a, htr124a, htr128a, htr289a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr236a, htr368a, htr567a, htr568a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd26a, hd34b, htr034a, htr036a, htr268a, htr368a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd23a, hd67b, htr035a, htr036a, htr235a, htr367a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc023yx, hc467yz, htr024a, htr035a, htr247c, htr279a, htr356a, htr479a, htr567a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc013yx, hc789yz, htr014a, htr035a, htr147a, htr358a, htr479a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc256yz, htr268a, htr568c, htr589a, htr689a]
        ·
          linarith only [hlam, hc256yz, htr268b, htr289a, htr568a, htr689a]
    ·
      have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr035a, htr035b, htr035c, _, _⟩
        linarith only [hlam, hd25a, hd34b, htr034a, htr035a, htr256a, htr356a])
      obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd23a, hd57b, htr035a, htr036a, htr236a, htr357a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc235yz, htr256b, htr268a, htr356a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd25a, hd67b, htr256a, htr367a, htr368a, htr568a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc235yz, htr256b, htr269a, htr356a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hd25a, hd67b, htr256a, htr367a, htr369a, htr569a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd25a, hd78b, htr256a, htr356a, htr357a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd23a, hd57b, htr123a, htr127a, htr278a, htr578a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd25a, hd79b, htr256a, htr356a, htr357a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hd23a, hd57b, htr123a, htr127a, htr279a, htr579a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hd25a, hd710b, htr256a, htr356a, htr357a, htr5710a])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hd23a, hd57b, htr123a, htr127a, htr2710a, htr5710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      rcases m.htr 4 7 8 (by decide) (by decide) with
        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
      ·
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc025yx, hc457yz, htr024a, htr056a, htr247c, htr278a, htr356a, htr357a, htr478a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc457yz, htr057a, htr058a, htr478a, htr578b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd02b, hd79a, htr024a, htr247c, htr278a, htr478a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc457yz, htr057a, htr059a, htr479a, htr579b])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd25a, hd89b, htr056a, htr058a, htr256a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd25a, hd910b, htr056a, htr059a, htr256a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc457yz, htr478a, htr578c, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc457yz, htr479a, htr579c, htr5910a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd02b, hd89a, htr024a, htr247c, htr279a, htr7910a, htr8910a]
        ·
          linarith only [hlam, hd02b, hd910a, htr024a, htr247c, htr278a, htr789a, htr8910a]
      ·
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd02b, hd78a, htr024a, htr247c, htr279a, htr478a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hd02b, hd78a, htr024a, htr247c, htr2710a, htr4710a, htr478a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc013yx, hc789yz, htr014a, htr036a, htr147a, htr368a, htr479a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc013yx, hc7910yz, htr014a, htr036a, htr147a, htr369a, htr4710a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr014a, htr147a, htr478a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd01b, hd910a, htr014a, htr147a, htr479a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
  ·
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd02b, hd78a, htr024a, htr124a, htr127a, htr278a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd02b, hd79a, htr024a, htr124a, htr127a, htr279a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
      linarith only [hlam, hd02b, hd710a, htr024a, htr124a, htr127a, htr2710a])
    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
    rcases m.htr 1 2 8 (by decide) (by decide) with
      ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
    ·
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc235yz, htr125a, htr128a, htr258c, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc236yz, htr126a, htr128a, htr268c, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc256yz, htr126a, htr128a, htr268c, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc257yz, htr127a, htr128a, htr278c, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc267yz, htr127a, htr128a, htr278c, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr235a, htr356a, htr567a, htr678a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd25a, hd34b, htr034a, htr035a, htr256a, htr356a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd23a, hd58b, htr035a, htr036a, htr236a, htr358a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hd25a, hd78b, htr256a, htr356a, htr357a, htr578a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hd25a, hd68b, htr256a, htr367a, htr368a, htr567a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc235yz, htr257b, htr279a, htr357a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd25a, hd89b, htr256a, htr356a, htr358a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd23a, hd58b, htr123a, htr128a, htr289a, htr589a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc023yx, hc478yz, htr024a, htr036a, htr248c, htr289a, htr367a, htr489a, htr678a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc013yx, hc789zy, htr014a, htr036a, htr148a, htr367a, htr489a, htr679a]
        ·
          linarith only [hlam, hd25a, hd78b, htr257a, htr579a, htr678a, htr679a]
      ·
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc235yz, htr256b, htr267a, htr356a, htr567a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hd25a, hd68b, htr257a, htr356a, htr357a, htr568a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hd23a, hd68b, htr236a, htr367a, htr567a, htr568a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd26a, hd34b, htr034a, htr036a, htr267a, htr367a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd23a, hd68b, htr035a, htr036a, htr235a, htr368a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc256yz, htr267b, htr279a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd26a, hd78b, htr267a, htr578a, htr579a, htr679a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc013yx, hc789zy, htr014a, htr035a, htr148a, htr357a, htr489a, htr579a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc023yx, hc468yz, htr024a, htr035a, htr248c, htr289a, htr356a, htr489a, htr568a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd26a, hd89b, htr267a, htr567a, htr568a, htr678c, htr789a]
        ·
          linarith only [hlam, hd23a, hd78b, htr123a, htr128a, htr289a, htr789a]
    ·
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hd02b, hd89a, htr024a, htr124a, htr128a, htr289a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
        linarith only [hlam, hd02b, hd810a, htr024a, htr124a, htr128a, htr2810a])
      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
      rcases m.htr 1 2 9 (by decide) (by decide) with
        ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
      ·
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc256yz, htr126a, htr129a, htr269c, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc257yz, htr127a, htr129a, htr279c, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc267yz, htr127a, htr129a, htr279c, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc278yz, htr128a, htr129a, htr289c, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hd23a, hd79b, htr235a, htr356a, htr567a, htr679a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hd25a, hd79b, htr256a, htr356a, htr357a, htr579a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc235yz, htr257b, htr278a, htr357a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd25a, hd89b, htr256a, htr567a, htr678a, htr789a]
          ·
            linarith only [hlam, hd25a, hd79b, htr257a, htr578a, htr678a, htr679a]
        ·
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc235yz, htr256b, htr267a, htr356a, htr567a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hd25a, hd69b, htr257a, htr356a, htr357a, htr569a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd23a, hd89b, htr235a, htr357a, htr578a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd26a, hd79b, htr267a, htr578a, htr579a, htr678a]
          ·
            linarith only [hlam, hc256yz, htr267b, htr278a, htr567a, htr678a]
      ·
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, hd02b, hd910a, htr024a, htr124a, htr129a, htr2910a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        rcases m.htr 1 2 10 (by decide) (by decide) with
          ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
        ·
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, hc256yz, htr1210a, htr126a, htr2610c, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hc257yz, htr1210a, htr127a, htr2710c, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc267yz, htr1210a, htr127a, htr2710c, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc278yz, htr1210a, htr128a, htr2810c, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hd23a, hd710b, htr235a, htr356a, htr567a, htr6710a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hd25a, hd710b, htr256a, htr356a, htr357a, htr5710a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc235yz, htr257b, htr278a, htr357a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd25a, hd810b, htr256a, htr567a, htr678a, htr7810a]
            ·
              linarith only [hlam, hd25a, hd710b, htr257a, htr578a, htr6710a, htr678a]
          ·
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc235yz, htr256b, htr267a, htr356a, htr567a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hd25a, hd610b, htr257a, htr356a, htr357a, htr5610a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd23a, hd810b, htr235a, htr357a, htr578a, htr7810a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd26a, hd710b, htr267a, htr5710a, htr578a, htr678a]
            ·
              linarith only [hlam, hc256yz, htr267b, htr278a, htr567a, htr678a]
        ·
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hd23a, hd78b, htr235a, htr356a, htr567a, htr678a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                linarith only [hlam, hd25a, hd34b, htr034a, htr035a, htr256a, htr356a])
              obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hc235yz, htr035a, htr036a, htr256a, htr356b])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              rcases m.htr 3 6 7 (by decide) (by decide) with
                ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
              ·
                linarith only [hlam, hc023yx, hc278yz, htr024a, htr036a, htr124a, htr128a, htr367a, htr678a]
              ·
                linarith only [hlam, hc235yz, htr256a, htr356c, htr367a, htr567a]
            ·
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc236yz, htr267b, htr278a, htr367a, htr678a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc267yz, htr278a, htr367a, htr368a, htr678b])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc267yz, htr278a, htr567a, htr568a, htr678b])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc267yz, htr278b, htr289a, htr678a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc267yz, htr278a, htr368c, htr389a, htr678c, htr789a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc267yz, htr278a, htr678c, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hc023yx, hc289yz, htr024a, htr036a, htr124a, htr129a, htr368a, htr689a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hd23a, hd89b, htr036a, htr038a, htr236a, htr389a])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hd23a, hd89b, htr235a, htr356a, htr568a, htr689a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              rcases m.htr 0 3 5 (by decide) (by decide) with
                ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
              ·
                linarith only [hlam, hc235yz, htr035a, htr038a, htr256a, htr356b, htr368b]
              ·
                linarith only [hlam, hd25a, hd34b, htr034a, htr035a, htr256a, htr356a]
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc025zy, htr056a, htr256b, htr267a, htr567a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc256yz, htr056a, htr057a, htr267a, htr567b])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc235yz, htr256b, htr267a, htr356a, htr567a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hc256yz, htr267a, htr356a, htr357a, htr567b])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hc256yz, htr267b, htr278a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc256yz, htr267a, htr357c, htr378a, htr567c, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc256yz, htr267a, htr567c, htr578a, htr678a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr035a, htr035b, htr035c, _, _⟩
              linarith only [hlam, hc023yx, hc278yz, htr024a, htr035a, htr124a, htr128a, htr357a, htr578a])
            obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd23a, hd78b, htr035a, htr037a, htr235a, htr378a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hd27a, hd34b, htr034a, htr037a, htr279a, htr379a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd23a, hd78b, htr237a, htr379a, htr578a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc025yx, hc289yz, htr024a, htr057a, htr124a, htr129a, htr578a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hc025yx, hc2910yz, htr024a, htr057a, htr1210a, htr124a, htr579a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hc278yz, htr289a, htr789c, htr7910a, htr8910a]
            ·
              linarith only [hlam, hc278yz, htr289b, htr2910a, htr789a, htr8910a]

theorem shard_581 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr147a : m.d 4 7 + lam ≤ m.d 1 4)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr248c : m.d 2 8 < m.d 2 4)
    (htr256a : m.d 2 5 + lam ≤ m.d 5 6)
    (htr256b : m.d 2 5 < m.d 2 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr258a : m.d 2 5 + lam ≤ m.d 5 8)
    (htr258c : m.d 2 8 < m.d 5 8)
    : False :=
  proof_shard_581 m htr014a htr024a htr027b htr034a htr123a htr124a htr125a htr126a htr147a htr148a htr235a htr236a htr237a htr237c htr239c htr247c htr248c htr256a htr256b htr257a htr257b htr257c htr258a htr258c

#print axioms shard_581
end Jsp404.NoSatElevenDBMTerminal
