import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_592 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr157b : m.d 1 5 < m.d 1 7)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr248a : m.d 2 4 + lam ≤ m.d 4 8)
    (htr249a : m.d 2 4 + lam ≤ m.d 4 9)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr258a : m.d 2 5 + lam ≤ m.d 5 8)
    (htr258b : m.d 2 5 < m.d 2 8)
    (htr258c : m.d 2 8 < m.d 5 8)
    (htr259a : m.d 2 5 + lam ≤ m.d 5 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
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
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd25a := (m.hrange 2 5 (by decide)).1
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
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
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5810xy, hc5810yx, hc5810yz, hc5810zy⟩ := endpoint_caps m 5 8 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hd24a, hd56b, htr247a, htr345a, htr347a, htr456a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hd24a, hd56b, htr248a, htr345a, htr348a, htr456a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, hd24a, hd56b, htr249a, htr345a, htr349a, htr456a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd23a, hd67b, htr234a, htr345a, htr456a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr267a, htr567a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc236xy, htr123a, htr126b, htr167a, htr267a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd23a, hd68b, htr234a, htr345a, htr456a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr268a, htr568a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hc236xy, htr123a, htr126b, htr168a, htr268a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hd23a, hd69b, htr234a, htr345a, htr456a, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr269a, htr569a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, hc236xy, htr123a, htr126b, htr169a, htr269a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  rcases m.htr 4 5 7 (by decide) (by decide) with
    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
  ·
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd23a, hd78b, htr234a, htr345a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd23a, hd57b, htr234a, htr347a, htr478a, htr578a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd23a, hd79b, htr234a, htr345a, htr457a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd23a, hd57b, htr234a, htr347a, htr479a, htr579a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
      linarith only [hlam, hd23a, hd710b, htr234a, htr345a, htr457a, htr5710a])
    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc567zy, htr457a, htr458a, htr578b, htr678a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd23a, hd89b, htr234a, htr345a, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
        linarith only [hlam, hd23a, hd810b, htr234a, htr345a, htr458a, htr5810a])
      obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hc567zy, htr268b, htr289a, htr578a, htr678b, htr789a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        linarith only [hlam, hc567zy, htr578c, htr5810a, htr678a, htr7810a])
      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hc567zy, htr578a, htr678b, htr6810a, htr7810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        linarith only [hlam, hd01b, hd910a, htr016a, htr168a, htr689a, htr8910a])
      obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr016a, htr169a, htr6910a, htr8910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc567zy, htr457a, htr459a, htr579b, htr679a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hc013yx, hc589zy, htr016a, htr034a, htr168a, htr345a, htr459a, htr689a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc236xy, hc589zy, htr126a, htr128a, htr234a, htr289a, htr345a, htr459a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc023zy, htr038a, htr123a, htr128a, htr238c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd23a, hd57b, htr034a, htr038a, htr234a, htr378c, htr578a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr378a, htr379a, htr789c])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, hc467zy, htr038a, htr039a, htr348c, htr379b, htr478c, htr679a])
        obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hd23a, hd910b, htr034a, htr039a, htr234a, htr3910a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc467zy, htr349c, htr3910a, htr479c, htr679a, htr7910a]
        ·
          linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a]
      ·
        rcases m.htr 6 7 10 (by decide) (by decide) with
          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        ·
          have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
            linarith only [hlam, hc567zy, htr4510a, htr457a, htr5710b, htr6710a])
          obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hc013yx, hc5810zy, htr016a, htr034a, htr168a, htr345a, htr4510a, htr6810a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc236xy, htr023c, htr026a, htr034a, htr234a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, hd02b, hd79a, htr026a, htr126a, htr127a, htr267b, htr679a])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          rcases m.htr 2 7 10 (by decide) (by decide) with
            ⟨htr2710a, htr2710b, htr2710c, _, _⟩ | ⟨htr2710a, htr2710b, htr2710c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd57b, htr123a, htr127a, htr2710a, htr5710a]
          ·
            linarith only [hlam, hd02b, hd79a, htr026a, htr267c, htr2710a, htr6710a, htr679a]
        ·
          rcases m.htr 0 3 4 (by decide) (by decide) with
            ⟨htr034a, htr034b, htr034c, _, _⟩ | ⟨htr034a, htr034b, htr034c, _, _⟩
          ·
            have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr459a, htr459b, htr459c, _, _⟩
              linarith only [hlam, hc013yx, hc589zy, htr016a, htr034a, htr168a, htr345a, htr459a, htr689a])
            obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hc013yx, hc8910yz, htr016a, htr034a, htr168a, htr349a, htr4910a, htr6810a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            rcases m.htr 5 9 10 (by decide) (by decide) with
              ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            ·
              linarith only [hlam, hc245yz, htr259a, htr459c, htr4910a, htr5910a]
            ·
              linarith only [hlam, hd56b, hd89a, htr456a, htr459a, htr5910a, htr8910a]
          ·
            have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr026a, htr026b, htr026c, _, _⟩
              linarith only [hlam, hc236xy, htr023c, htr026a, htr034a, htr234a])
            obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
            have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr127a, htr127b, htr127c, _, _⟩
              linarith only [hlam, hd02b, hd79a, htr026a, htr126a, htr127a, htr267b, htr679a])
            obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
            rcases m.htr 2 7 8 (by decide) (by decide) with
              ⟨htr278a, htr278b, htr278c, _, _⟩ | ⟨htr278a, htr278b, htr278c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd57b, htr123a, htr127a, htr278a, htr578a]
            ·
              linarith only [hlam, hd02b, hd79a, htr026a, htr267c, htr278a, htr678a, htr679a]
    ·
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr016a, htr167a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        linarith only [hlam, hd01b, hd810a, htr016a, htr167a, htr678a, htr7810a])
      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc567zy, htr457a, htr459a, htr579b, htr679a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc478zy, htr489a, htr678a, htr679a, htr789c])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc578zy, htr589a, htr678a, htr679a, htr789c])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr234a, htr345a, htr458a, htr589a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hd23a, hd56b, htr235a, htr358a, htr456a, htr458a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd25a, hd36b, htr035a, htr036a, htr258a, htr358a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hd23a, hd56b, htr034a, htr035a, htr234a, htr356a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr5810a, htr7810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hd25a, hd89b, htr258a, htr4810a, htr489a, htr5810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd23a, hd910b, htr234a, htr345a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc013yx, hc8910zy, htr016a, htr034a, htr169a, htr348a, htr4810a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc567zy, htr579c, htr5910a, htr679a, htr7910a]
        ·
          linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a]
      ·
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd01b, hd910a, htr016a, htr167a, htr679a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hc013yx, hc578zy, htr016a, htr034a, htr167a, htr345a, htr458a, htr678a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hd23a, hd56b, htr034a, htr035a, htr234a, htr356a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr359a, htr359b, htr359c, _, _⟩
            linarith only [hlam, hd25a, hd36b, htr035a, htr036a, htr259a, htr359a])
          obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, hd23a, hd56b, htr235a, htr359a, htr456a, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd23a, hd89b, htr234a, htr345a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr234a, htr345a, htr459a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a]
          ·
            linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a]
        ·
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hd23a, hd56b, htr235a, htr358a, htr456a, htr458a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr035a, htr035b, htr035c, _, _⟩
            linarith only [hlam, hd25a, hd36b, htr035a, htr036a, htr258a, htr358a])
          obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hd23a, hd56b, htr034a, htr035a, htr234a, htr356a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc013yx, hc789yz, htr016a, htr034a, htr167a, htr348a, htr489a, htr679a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          rcases m.htr 5 8 9 (by decide) (by decide) with
            ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
          ·
            linarith only [hlam, hc245yz, htr258a, htr458c, htr489a, htr589a]
          ·
            linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a]
  ·
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, hc245yz, htr125a, htr127a, htr257c, htr457a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd23a, hd56b, htr235a, htr357a, htr456a, htr457a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hd25a, hd36b, htr035a, htr036a, htr257a, htr357a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr034a, htr034b, htr034c, _, _⟩
      linarith only [hlam, hd23a, hd56b, htr034a, htr035a, htr234a, htr356a])
    obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, htr345c, htr358a, htr458a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr357c, htr358b, htr378c])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd23a, hd56b, htr237a, htr378a, htr456a, htr457c, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc236xy, hc789yx, htr126a, htr127a, htr234a, htr279a, htr347a, htr478a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hc236xy, hc7810yx, htr126a, htr127a, htr234a, htr2710a, htr347a, htr478a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc245yz, htr257b, htr279a, htr457a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc245yz, htr257a, htr457c, htr479a, htr579a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hc245yz, htr257b, htr2710a, htr457a, htr5710a])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hc245yz, htr257a, htr457c, htr4710a, htr5710a])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd23a, hd89b, htr234a, htr345a, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc013yx, hc789zy, htr016a, htr034a, htr168a, htr347a, htr479a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr359a, htr359b, htr359c, _, _⟩
        linarith only [hlam, hc568zy, htr345c, htr359a, htr458a, htr589b, htr689a])
      obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
      have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
        linarith only [hlam, hd25a, hd910b, htr257a, htr357a, htr359a, htr5910a])
      obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc013yx, hc7910zy, htr016a, htr034a, htr169a, htr347a, htr4710a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc568zy, htr589c, htr5910a, htr689a, htr8910a]
      ·
        linarith only [hlam, hc568zy, htr589a, htr689b, htr6910a, htr8910a]
    ·
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hc245yz, htr125a, htr128a, htr258c, htr458a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc245yz, htr257a, htr357a, htr358a, htr458a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      rcases m.htr 4 5 9 (by decide) (by decide) with
        ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
      ·
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, htr345c, htr359a, htr459a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr357c, htr359b, htr379c])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, htr358c, htr359b, htr389c])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd23a, hd56b, htr237a, htr379a, htr456a, htr457c, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc236xy, hc789xy, htr126a, htr127a, htr234a, htr278a, htr347a, htr479a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd23a, hd56b, htr238a, htr389a, htr456a, htr458c, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc245yz, htr257b, htr278a, htr457a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc245yz, htr257a, htr457c, htr478a, htr578a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
        ·
          linarith only [hlam, hd23a, hd78b, htr234a, htr348a, htr489a, htr789a]
      ·
        rcases m.htr 4 5 10 (by decide) (by decide) with
          ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
        ·
          have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
            linarith only [hlam, htr345c, htr3510a, htr4510a])
          obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr3510b, htr357c, htr3710c])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, htr3510b, htr358c, htr3810c])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, hd23a, hd56b, htr237a, htr3710a, htr456a, htr457c, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc236xy, hc7810xy, htr126a, htr127a, htr234a, htr278a, htr347a, htr4710a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hd23a, hd56b, htr238a, htr3810a, htr456a, htr458c, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc245yz, htr257b, htr278a, htr457a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc245yz, htr257a, htr457c, htr478a, htr578a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd810b, htr234a, htr347a, htr478a, htr7810a]
          ·
            linarith only [hlam, hd23a, hd78b, htr234a, htr348a, htr4810a, htr7810a]
        ·
          rcases m.htr 0 2 6 (by decide) (by decide) with
            ⟨htr026a, htr026b, htr026c, _, _⟩ | ⟨htr026a, htr026b, htr026c, _, _⟩
          ·
            have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr057a, htr057b, htr057c, _, _⟩
              linarith only [hlam, hc256xy, htr025c, htr026a, htr057a, htr257a])
            obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc245yz, htr257a, htr457c, htr478a, htr578a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hc236xy, hc789yx, htr126a, htr127a, htr234a, htr279a, htr347a, htr478a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc245yz, htr257b, htr279a, htr457a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc245yz, htr257a, htr457c, htr479a, htr579a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc236xy, hc789zy, htr126a, htr128a, htr234a, htr289a, htr347a, htr479a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc245yz, htr258b, htr289a, htr458a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc245yz, htr258a, htr458c, htr489a, htr589a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
              ·
                linarith only [hlam, hd23a, hd78b, htr234a, htr348a, htr489a, htr789a]
            ·
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc145yz, htr017b, htr078a, htr157b, htr457a, htr578a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc245yz, htr257b, htr278a, htr457a, htr578a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc236xy, hc789xy, htr126a, htr127a, htr234a, htr278a, htr347a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hd56b, hd78a, htr078a, htr079a, htr456a, htr457c, htr479a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hd56b, hd78a, htr057c, htr079a, htr278a, htr279a, htr456a, htr457a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc236xy, hc789yz, htr126a, htr127a, htr234a, htr279a, htr348a, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc245yz, htr258a, htr458c, htr489a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a]
              ·
                linarith only [hlam, hd56b, hd89a, htr456a, htr457a, htr578a, htr789a]
          ·
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hd02b, hd78a, htr026a, htr126a, htr127a, htr278a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc023yx, hc278yz, htr026a, htr034a, htr126a, htr128a, htr347a, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              linarith only [hlam, hc245yz, htr257a, htr457c, htr478a, htr578a]
            ·
              linarith only [hlam, hc245yz, htr257b, htr278a, htr457a, htr578a]

theorem shard_592 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr157b : m.d 1 5 < m.d 1 7)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr248a : m.d 2 4 + lam ≤ m.d 4 8)
    (htr249a : m.d 2 4 + lam ≤ m.d 4 9)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr258a : m.d 2 5 + lam ≤ m.d 5 8)
    (htr258b : m.d 2 5 < m.d 2 8)
    (htr258c : m.d 2 8 < m.d 5 8)
    (htr259a : m.d 2 5 + lam ≤ m.d 5 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    : False :=
  proof_shard_592 m htr016a htr017b htr023c htr025c htr036a htr123a htr125a htr126a htr126b htr157b htr234a htr235a htr237a htr238a htr238c htr247a htr248a htr249a htr257a htr257b htr257c htr258a htr258b htr258c htr259a htr345a htr345c htr356a htr456a

#print axioms shard_592
end Jsp404.NoSatElevenDBMTerminal
