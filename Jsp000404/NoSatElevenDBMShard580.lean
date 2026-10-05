import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_580 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr028b : m.d 2 8 < m.d 0 8)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr146a : m.d 4 6 + lam ≤ m.d 1 4)
    (htr147a : m.d 4 7 + lam ≤ m.d 1 4)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr258c : m.d 2 8 < m.d 5 8)
    (htr259c : m.d 2 9 < m.d 5 9)
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
  have hd27a := (m.hrange 2 7 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  obtain ⟨hd37a, hd37braw⟩ := m.hrange 3 7 (by decide)
  have hd37b : m.d 3 7 < 4*lam := by
    linarith only [hd37braw, hp]
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
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc046xy, hc046yx, hc046yz, hc046zy⟩ := endpoint_caps m 0 4 6 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc289xy, hc289yx, hc289yz, hc289zy⟩ := endpoint_caps m 2 8 9 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hc023zy, htr036a, htr123a, htr126a, htr236c])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc025zy, htr056a, htr125a, htr126a, htr256c])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc235yz, htr125a, htr126a, htr256c, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  rcases m.htr 1 2 7 (by decide) (by decide) with
    ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc023zy, htr037a, htr123a, htr127a, htr237c])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc235yz, htr125a, htr127a, htr257c, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    rcases m.htr 1 2 8 (by decide) (by decide) with
      ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc023zy, htr038a, htr123a, htr128a, htr238c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc025zy, htr058a, htr125a, htr128a, htr258c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc235yz, htr125a, htr128a, htr258c, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      rcases m.htr 1 2 9 (by decide) (by decide) with
        ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
      ·
        rcases m.htr 1 2 10 (by decide) (by decide) with
          ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
        ·
          rcases m.htr 0 3 5 (by decide) (by decide) with
            ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
          ·
            rcases m.htr 2 6 7 (by decide) (by decide) with
              ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
            ·
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, htr126c, htr167a, htr267a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr267a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd23a, hd78b, htr123a, htr126a, htr267a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr278a, htr678a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc023yx, hc467yz, htr024a, htr035a, htr247c, htr278a, htr356a, htr478a, htr567a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc013yx, hc678zy, htr014a, htr035a, htr147a, htr356a, htr478a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hd23a, hd67b, htr123a, htr126b, htr168a, htr567a, htr568a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc013yx, hc789xy, htr014a, htr035a, htr147a, htr357a, htr478a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc678yx, htr167b, htr168a, htr179a, htr567c, htr579a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc013yx, hc467yz, htr017a, htr035a, htr179a, htr356a, htr479a, htr567a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc013yx, hc789yz, htr014a, htr035a, htr147a, htr358a, htr479a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc678yx, htr567a, htr568c, htr589a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd67b, hd78a, htr567a, htr568a, htr689a, htr789a]
              ·
                linarith only [hlam, hd01b, hd89a, htr014a, htr147a, htr478a, htr789a]
            ·
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, htr026b, htr067a, htr267a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc236xy, htr123a, htr126b, htr167a, htr267a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, htr256c, htr267a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              rcases m.htr 4 6 7 (by decide) (by decide) with
                ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hd02b, hd68a, htr024a, htr246c, htr267a, htr467a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                rcases m.htr 5 6 8 (by decide) (by decide) with
                  ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, htr056c, htr068a, htr568a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, htr067c, htr068b, htr078c])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, htr156c, htr168a, htr568a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd23a, hd68b, htr027b, htr078a, htr123a, htr127a, htr567c, htr568a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc023yx, hc789yx, htr024a, htr035a, htr246c, htr267a, htr357a, htr578a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, hc046zy, htr067c, htr079a, htr467a, htr679a])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd23a, hd68b, htr027b, htr079a, htr123a, htr127a, htr567c, htr568a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc013yx, hc789zy, htr014a, htr035a, htr148a, htr357a, htr489a, htr579a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc013yx, hc468yz, htr018a, htr035a, htr189a, htr356a, htr489a, htr568a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd23a, hd89b, htr027b, htr078a, htr123a, htr127a, htr789a]
                  ·
                    linarith only [hlam, hd46a, hd78b, htr167a, htr168b, htr189a, htr467a, htr789a]
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc456yz, htr026b, htr068a, htr267a, htr467a, htr568a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, hc456yz, htr167a, htr168a, htr467a, htr568a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  rcases m.htr 5 6 9 (by decide) (by decide) with
                    ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
                  ·
                    have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                      linarith only [hlam, htr056c, htr069a, htr569a])
                    obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, htr067c, htr069b, htr079c])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr068c, htr069b, htr089c])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                      linarith only [hlam, hd23a, hd69b, htr027b, htr079a, htr123a, htr127a, htr567c, htr569a, htr579a])
                    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc023yx, hc789xy, htr024a, htr035a, htr246c, htr267a, htr357a, htr579a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hc046zy, htr067c, htr078a, htr467a, htr678a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd23a, hd89b, htr027b, htr078a, htr123a, htr127a, htr789a]
                    ·
                      linarith only [hlam, hd23a, hd78b, htr028b, htr089a, htr123a, htr128a, htr789a]
                  ·
                    rcases m.htr 5 6 10 (by decide) (by decide) with
                      ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                    ·
                      have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                        linarith only [hlam, htr056c, htr0610a, htr5610a])
                      obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, htr0610b, htr067c, htr0710c])
                      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, htr0610b, htr068c, htr0810c])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                        linarith only [hlam, hd23a, hd610b, htr027b, htr0710a, htr123a, htr127a, htr5610a, htr567c, htr5710a])
                      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc023yx, hc7810xy, htr024a, htr035a, htr246c, htr267a, htr357a, htr5710a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, hc046zy, htr067c, htr078a, htr467a, htr678a])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      rcases m.htr 7 8 10 (by decide) (by decide) with
                        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      ·
                        linarith only [hlam, hd23a, hd810b, htr027b, htr078a, htr123a, htr127a, htr7810a]
                      ·
                        linarith only [hlam, hd23a, hd78b, htr028b, htr0810a, htr123a, htr128a, htr7810a]
                    ·
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                          linarith only [hlam, hc046zy, htr067c, htr078a, htr467a, htr678a])
                        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                          linarith only [hlam, hc023yx, hc789yx, htr024a, htr035a, htr246c, htr267a, htr357a, htr578a, htr679a])
                        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, hc046zy, htr067c, htr079a, htr467a, htr679a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hd23a, hd78b, htr027b, htr079a, htr123a, htr127a, htr578a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc013yx, hc789zy, htr014a, htr035a, htr148a, htr357a, htr489a, htr579a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc013yx, hc478yz, htr018a, htr035a, htr189a, htr357a, htr489a, htr578a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, hc456yz, htr058c, htr089a, htr168b, htr189a, htr468a, htr568c])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd23a, hd89b, htr027b, htr078a, htr123a, htr127a, htr789a]
                        ·
                          linarith only [hlam, hd23a, hd78b, htr028b, htr089a, htr123a, htr128a, htr789a]
                      ·
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hd02b, hd47a, htr024a, htr246c, htr267a, htr478a, htr678a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hc023yx, hc789xy, htr024a, htr035a, htr246c, htr267a, htr357a, htr579a, htr678a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc456yz, htr167b, htr179a, htr467a, htr567c, htr579a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hd01b, hd78a, htr017a, htr179a, htr478a, htr479a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc013yx, hc789yz, htr014a, htr035a, htr147a, htr358a, htr479a, htr589a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc456yz, htr468a, htr568c, htr589a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd01b, hd78a, htr016a, htr168a, htr689a, htr789a]
                        ·
                          linarith only [hlam, hd02b, hd89a, htr024a, htr246c, htr267a, htr678a, htr789a]
              ·
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc013yx, hc678xy, htr014a, htr035a, htr146a, htr356a, htr467a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr268a, htr568a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hd02b, hd67a, htr024a, htr246c, htr268a, htr467a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hc013yx, hc679xy, htr014a, htr035a, htr146a, htr356a, htr467a, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                  linarith only [hlam, hd23a, hd56b, htr123a, htr126a, htr269a, htr569a])
                obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                  linarith only [hlam, hd02b, hd67a, htr024a, htr246c, htr269a, htr467a, htr469a])
                obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc013yx, hc678yz, htr014a, htr035a, htr146a, htr357a, htr468a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hd23a, hd57b, htr123a, htr127a, htr278a, htr578a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc013yx, hc689yz, htr014a, htr035a, htr146a, htr358a, htr469a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd01b, hd89a, htr014a, htr146a, htr468a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a]
                ·
                  linarith only [hlam, hd02b, hd68a, htr024a, htr247c, htr278a, htr689a, htr789a]
          ·
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hd23a, hd67b, htr035a, htr036a, htr235a, htr367a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hd23a, hd36b, htr123a, htr126a, htr267a, htr367a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hd23a, hd68b, htr035a, htr036a, htr235a, htr368a])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hd23a, hd36b, htr123a, htr126a, htr268a, htr368a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd23a, hd78b, htr035a, htr037a, htr235a, htr378a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hd23a, hd37b, htr123a, htr127a, htr278a, htr378a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hd23a, hd89b, htr035a, htr038a, htr235a, htr389a])
            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc346zy, htr367c, htr378a, htr467a, htr678a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd02b, hd67a, htr024a, htr246c, htr268a, htr467a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd01b, hd89a, htr014a, htr146a, htr468a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc367zy, htr378c, htr389a, htr678a, htr789a]
              ·
                linarith only [hlam, hd02b, hd68a, htr024a, htr247c, htr278a, htr689a, htr789a]
            ·
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd02b, hd68a, htr024a, htr246c, htr267a, htr467a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc346zy, htr368c, htr389a, htr468a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd02b, hd78a, htr024a, htr246c, htr268a, htr689a, htr789a]
              ·
                linarith only [hlam, hd02b, hd89a, htr024a, htr246c, htr267a, htr678a, htr789a]
        ·
          have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
            linarith only [hlam, htr1210c, htr126b, htr1610b])
          obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
            linarith only [hlam, htr1210c, htr127b, htr1710b])
          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
          have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
            linarith only [hlam, htr126c, htr1610a, htr2610a])
          obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc6710yx, htr1210a, htr126a, htr2610b, htr267a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
            linarith only [hlam, htr127c, htr1710a, htr2710a])
          obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, hd02b, hd46a, htr024a, htr1210a, htr124a, htr2610b, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd02b, hd610a, htr024a, htr246c, htr267a, htr4610a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          rcases m.htr 6 7 10 (by decide) (by decide) with
            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          ·
            linarith only [hlam, hd02b, hd67a, htr024a, htr1210a, htr124a, htr2710b, htr6710a]
          ·
            linarith only [hlam, hd01b, hd710a, htr014a, htr146a, htr467a, htr6710a]
      ·
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, htr126b, htr129c, htr169b])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, htr127b, htr129c, htr179b])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, htr126c, htr169a, htr269a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc679yx, htr126a, htr129a, htr267a, htr269b])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, htr127c, htr179a, htr279a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hd02b, hd46a, htr024a, htr124a, htr129a, htr269b, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd02b, hd69a, htr024a, htr246c, htr267a, htr467a, htr469a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hd02b, hd67a, htr024a, htr124a, htr129a, htr279b, htr679a]
        ·
          linarith only [hlam, hd01b, hd79a, htr014a, htr146a, htr467a, htr679a]
    ·
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr126b, htr128c, htr168b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr127b, htr128c, htr178b])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr126c, htr168a, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc678yx, htr126a, htr128a, htr267a, htr268b])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr127c, htr178a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd02b, hd46a, htr024a, htr124a, htr128a, htr268b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd02b, hd68a, htr024a, htr246c, htr267a, htr467a, htr468a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hd02b, hd67a, htr024a, htr124a, htr128a, htr278b, htr678a]
      ·
        linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a]
  ·
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr126b, htr127c, htr167b])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
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
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd02b, hd46a, htr024a, htr124a, htr127a, htr267b, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd02b, hd67a, htr024a, htr246c, htr268a, htr467a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd02b, hd67a, htr024a, htr246c, htr269a, htr467a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
      linarith only [hlam, hd02b, hd67a, htr024a, htr246c, htr2610a, htr4610a, htr467a])
    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
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
      linarith only [hlam, hd01b, hd89a, htr014a, htr146a, htr468a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
      linarith only [hlam, hd01b, hd810a, htr014a, htr146a, htr468a, htr6810a])
    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
      linarith only [hlam, hd01b, hd910a, htr014a, htr146a, htr469a, htr6910a])
    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
    rcases m.htr 1 2 8 (by decide) (by decide) with
      ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc023zy, htr038a, htr123a, htr128a, htr238c])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc235yz, htr125a, htr128a, htr258c, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc237yz, htr127a, htr128a, htr278c, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc257yz, htr127a, htr128a, htr278c, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        rcases m.htr 3 5 7 (by decide) (by decide) with
          ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd89b, htr235a, htr357a, htr578a, htr789a]
        ·
          linarith only [hlam, hd25a, hd89b, htr257a, htr357a, htr358a, htr578c, htr789a]
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr123a, htr128a, htr289a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, hc368zy, htr038a, htr039a, htr239c, htr289b, htr689a])
        obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc568zy, htr259c, htr289b, htr358a, htr359a, htr689a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc678yz, htr378a, htr379a, htr689a, htr789b])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc678yz, htr578a, htr579a, htr689a, htr789b])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a])
        obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hc678yz, htr379c, htr3910a, htr689a, htr789c, htr8910a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr035a, htr035b, htr035c, _, _⟩
          linarith only [hlam, hd23a, hd910b, htr035a, htr039a, htr235a, htr3910a])
        obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc013yx, hc6910yz, htr014a, htr035a, htr146a, htr359a, htr4610a, htr579c, htr7910a]
        ·
          linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
    ·
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd02b, hd68a, htr024a, htr124a, htr128c, htr189a, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hd02b, hd68a, htr024a, htr124a, htr128c, htr1810a, htr6810a])
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
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc257yz, htr127a, htr129a, htr279c, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc278yz, htr128a, htr129a, htr289c, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          rcases m.htr 5 7 8 (by decide) (by decide) with
            ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
          ·
            linarith only [hlam, hd25a, hd910b, htr257a, htr578a, htr789a, htr8910a]
          ·
            linarith only [hlam, hd27a, hd910b, htr278a, htr578a, htr579a, htr789c, htr8910a]
        ·
          rcases m.htr 5 7 8 (by decide) (by decide) with
            ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
          ·
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hd23a, hd89b, htr235a, htr357a, htr578a, htr789a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr035a, htr035b, htr035c, _, _⟩
              linarith only [hlam, hd25a, hd34b, htr034a, htr035a, htr257a, htr357a])
            obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd23a, hd56b, htr035a, htr037a, htr237a, htr356a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            rcases m.htr 3 7 8 (by decide) (by decide) with
              ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
            ·
              linarith only [hlam, hc013yx, hc689yz, htr014a, htr037a, htr146a, htr378a, htr469a, htr789a]
            ·
              linarith only [hlam, hd25a, hd79b, htr257a, htr378a, htr379a, htr578a]
          ·
            have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr357a, htr357b, htr357c, _, _⟩
              linarith only [hlam, hc235yz, htr257b, htr278a, htr357a, htr578a])
            obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
            have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr035a, htr035b, htr035c, _, _⟩
              linarith only [hlam, hc013yx, hc679yz, htr014a, htr035a, htr146a, htr357a, htr469a, htr579a])
            obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hd23a, hd79b, htr035a, htr037a, htr235a, htr379a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            rcases m.htr 3 7 8 (by decide) (by decide) with
              ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr578a, htr579a]
            ·
              linarith only [hlam, hd27a, hd34b, htr034a, htr037a, htr278a, htr378a]
      ·
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hd02b, hd69a, htr024a, htr124a, htr129c, htr1910a, htr6910a])
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
              linarith only [hlam, hd27a, hd34b, htr034a, htr037a, htr278a, htr378a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr038a, htr038b, htr038c, _, _⟩
              linarith only [hlam, hd23a, hd710b, htr037a, htr038a, htr238a, htr3710a])
            obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
            rcases m.htr 3 8 9 (by decide) (by decide) with
              ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
            ·
              linarith only [hlam, hc013yx, hc6910yz, htr014a, htr038a, htr146a, htr389a, htr4610a, htr8910a]
            ·
              linarith only [hlam, hd27a, hd810b, htr278a, htr3810a, htr389a, htr789a]
          ·
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr037a, htr037b, htr037c, _, _⟩
              linarith only [hlam, hc013yx, hc6810yz, htr014a, htr037a, htr146a, htr378a, htr4610a, htr7810a])
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
              linarith only [hlam, hd34b, hd68a, htr034a, htr038a, htr389a, htr689a]
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
                linarith only [hlam, hd27a, hd34b, htr034a, htr037a, htr278a, htr378a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr038a, htr038b, htr038c, _, _⟩
                linarith only [hlam, hc237yz, htr037a, htr038a, htr278a, htr378b])
              obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
              rcases m.htr 3 8 9 (by decide) (by decide) with
                ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
              ·
                linarith only [hlam, hc013yx, hc6910yz, htr014a, htr038a, htr146a, htr389a, htr4610a, htr8910a]
              ·
                linarith only [hlam, hc237yz, htr278a, htr378c, htr389a, htr789a]
            ·
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568zy, htr589a, htr689b, htr6910a, htr8910a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, hd23a, hd89b, htr235a, htr357a, htr578a, htr789a])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                  linarith only [hlam, hd25a, hd34b, htr034a, htr035a, htr257a, htr357a])
                obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
                have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                  linarith only [hlam, hd23a, hd56b, htr035a, htr037a, htr237a, htr356a])
                obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                rcases m.htr 3 7 8 (by decide) (by decide) with
                  ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
                ·
                  linarith only [hlam, hc013yx, hc689yz, htr014a, htr037a, htr146a, htr378a, htr469a, htr789a]
                ·
                  linarith only [hlam, hc235yz, htr257a, htr357c, htr378a, htr578a]
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc025zy, htr057a, htr257b, htr278a, htr578a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc257yz, htr057a, htr058a, htr278a, htr578b])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, hc235yz, htr257b, htr278a, htr357a, htr578a])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                  linarith only [hlam, hc257yz, htr278a, htr357a, htr358a, htr578b])
                obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr035a, htr035b, htr035c, _, _⟩
                  linarith only [hlam, hc013yx, hc689yz, htr014a, htr035a, htr146a, htr358a, htr469a, htr589a])
                obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
                have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                  linarith only [hlam, hc015yx, hc689yz, htr014a, htr058a, htr146a, htr469a, htr589b, htr5910a, htr8910a])
                obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  rcases m.htr 5 7 9 (by decide) (by decide) with
                    ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                  ·
                    linarith only [hlam, hd27a, hd89b, htr278a, htr578a, htr579a, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hc257yz, htr279a, htr579c, htr5910a, htr7910a]
                ·
                  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                    linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                    linarith only [hlam, hd23a, hd79b, htr035a, htr037a, htr235a, htr379a])
                  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hd27a, hd34b, htr034a, htr037a, htr278a, htr378a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  rcases m.htr 5 7 9 (by decide) (by decide) with
                    ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                  ·
                    linarith only [hlam, hd23a, hd79b, htr237a, htr378a, htr578a, htr579a]
                  ·
                    linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a]
          ·
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc678yz, htr378a, htr379a, htr689a, htr789b])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hc678yz, htr578a, htr579a, htr689a, htr789b])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
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
              linarith only [hlam, hc013yx, hc6910yz, htr014a, htr037a, htr146a, htr379a, htr4610a, htr7910a])
            obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
            have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr035a, htr035b, htr035c, _, _⟩
              linarith only [hlam, hd23a, hd56b, htr035a, htr037a, htr237a, htr356a])
            obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
            rcases m.htr 3 5 7 (by decide) (by decide) with
              ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd910b, htr235a, htr357a, htr579a, htr7910a]
            ·
              linarith only [hlam, hd25a, hd34b, htr034a, htr035a, htr257a, htr357a]

theorem shard_580 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr028b : m.d 2 8 < m.d 0 8)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr146a : m.d 4 6 + lam ≤ m.d 1 4)
    (htr147a : m.d 4 7 + lam ≤ m.d 1 4)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr257a : m.d 2 5 + lam ≤ m.d 5 7)
    (htr257b : m.d 2 5 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr258c : m.d 2 8 < m.d 5 8)
    (htr259c : m.d 2 9 < m.d 5 9)
    : False :=
  proof_shard_580 m htr014a htr016a htr017a htr018a htr024a htr026b htr027b htr028b htr034a htr123a htr124a htr125a htr126a htr126b htr126c htr146a htr147a htr148a htr156c htr235a htr236c htr237a htr237c htr238a htr238c htr239c htr246c htr247c htr256c htr257a htr257b htr257c htr258c htr259c

#print axioms shard_580
end Jsp404.NoSatElevenDBMTerminal
