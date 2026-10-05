import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_033 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr039a : m.d 3 9 + lam ≤ m.d 0 3)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr048a : m.d 4 8 + lam ≤ m.d 0 4)
    (htr048b : m.d 4 8 < m.d 0 8)
    (htr049b : m.d 4 9 < m.d 0 9)
    (htr057c : m.d 0 7 < m.d 5 7)
    (htr058c : m.d 0 8 < m.d 5 8)
    (htr059c : m.d 0 9 < m.d 5 9)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr156a : m.d 1 5 + lam ≤ m.d 5 6)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr158a : m.d 1 5 + lam ≤ m.d 5 8)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr239a : m.d 3 9 + lam ≤ m.d 2 3)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246b : m.d 4 6 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr248c : m.d 2 8 < m.d 2 4)
    (htr249a : m.d 4 9 + lam ≤ m.d 2 4)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr258c : m.d 2 8 < m.d 5 8)
    (htr259c : m.d 2 9 < m.d 5 9)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
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
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc248xy, hc248yx, hc248yz, hc248zy⟩ := endpoint_caps m 2 4 8 (by decide) (by decide)
  obtain ⟨hc258xy, hc258yx, hc258yz, hc258zy⟩ := endpoint_caps m 2 5 8 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  rcases m.htr 3 4 7 (by decide) (by decide) with
    ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
  ·
    rcases m.htr 3 4 8 (by decide) (by decide) with
      ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
    ·
      rcases m.htr 3 4 9 (by decide) (by decide) with
        ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
      ·
        rcases m.htr 3 4 10 (by decide) (by decide) with
          ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
        ·
          rcases m.htr 4 6 7 (by decide) (by decide) with
            ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
          ·
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc234zy, htr246c, htr267a, htr346a, htr467a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd45a, hd78b, htr345a, htr346a, htr467a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hd45a, hd79b, htr345a, htr346a, htr467a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr479a, htr679a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd01a, hd89b, htr015a, htr156a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hd45a, hd68b, htr345a, htr348a, htr489a, htr689a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd01a, hd810b, htr015a, htr156a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hd45a, hd68b, htr345a, htr348a, htr4810a, htr6810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc245yx, hc678zy, htr125a, htr126a, htr248a, htr256c, htr489a, htr568a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hc245yx, hc689zy, htr125a, htr126a, htr247a, htr269a, htr478a, htr789a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc245yx, hc678zy, htr125a, htr126a, htr248a, htr256c, htr4810a, htr568a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                linarith only [hlam, hc245yx, hc8910yz, htr125a, htr129a, htr247a, htr2910a, htr478a, htr7810a])
              obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc679yx, htr267a, htr269c, htr2910a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd67b, hd89a, htr267a, htr269a, htr6910a, htr8910a]
              ·
                linarith only [hlam, hd24b, hd910a, htr247a, htr478a, htr789a, htr8910a]
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd45a, hd67b, htr046b, htr068a, htr345a, htr346a, htr567a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd45a, hd67b, htr345a, htr346b, htr368a, htr567a, htr568a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              rcases m.htr 5 6 9 (by decide) (by decide) with
                ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, htr016c, htr069a, htr156c, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, htr068c, htr069b, htr089c])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hd45a, hd67b, htr048b, htr089a, htr258c, htr289a, htr345a, htr348a, htr567a, htr568c])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                  linarith only [hlam, htr136b, htr156c, htr369a, htr569a])
                obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc235yx, hc8910yx, htr125a, htr128a, htr236a, htr289a, htr368a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, hc678yx, htr058c, htr0810a, htr567a, htr568c, htr6810a])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hd45a, hd67b, htr048b, htr0810a, htr258c, htr2810a, htr345a, htr348a, htr567a, htr568c])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd01a, hd910b, htr015a, htr156a, htr569a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                  linarith only [hlam, hc689xy, htr368a, htr369b, htr3910a, htr6910a])
                obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc235yx, hc679zy, htr125a, htr126a, htr239a, htr256c, htr3910a, htr569a, htr7910a]
                ·
                  linarith only [hlam, hc245yx, hc8910zy, htr125a, htr128a, htr247a, htr2810a, htr479a, htr7910a]
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hd45a, hd67b, htr046b, htr069a, htr345a, htr346a, htr567a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                  linarith only [hlam, hc678yx, htr368a, htr369a, htr567a, htr569a])
                obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                rcases m.htr 5 6 10 (by decide) (by decide) with
                  ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                ·
                  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                    linarith only [hlam, htr016c, htr0610a, htr156c, htr5610a])
                  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                    linarith only [hlam, htr0610b, htr068c, htr0810c])
                  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                    linarith only [hlam, htr0610b, htr069c, htr0910c])
                  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                  have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                    linarith only [hlam, hd45a, hd67b, htr048b, htr0810a, htr258c, htr2810a, htr345a, htr348a, htr567a, htr568c])
                  obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc235yx, hc8910xy, htr125a, htr128a, htr236a, htr2810a, htr368a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, hc678yx, htr058c, htr089a, htr567a, htr568c, htr689a])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd45a, hd910b, htr048b, htr089a, htr345a, htr348a, htr8910a]
                  ·
                    linarith only [hlam, hd45a, hd89b, htr049b, htr0910a, htr345a, htr349a, htr8910a]
                ·
                  rcases m.htr 5 8 9 (by decide) (by decide) with
                    ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
                  ·
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc013xy, hc8910yx, htr015a, htr036a, htr158a, htr368a, htr589a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc678yx, htr058c, htr0810a, htr567a, htr568c, htr6810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                      linarith only [hlam, hd45a, hd67b, htr048b, htr0810a, htr258c, htr2810a, htr345a, htr348a, htr567a, htr568c])
                    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc235yx, hc8910zy, htr125a, htr128a, htr236a, htr2810a, htr369a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                      linarith only [hlam, hc679yx, htr059c, htr0910a, htr567a, htr569c, htr6910a])
                    obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd01a, hd910b, htr015a, htr158a, htr589a, htr8910a]
                    ·
                      linarith only [hlam, hd45a, hd89b, htr049b, htr0910a, htr345a, htr349a, htr8910a]
                  ·
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hc678yx, htr567a, htr568c, htr589a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                      linarith only [hlam, hc235yx, hc8910xy, htr125a, htr128a, htr236a, htr2810a, htr368a, htr689a])
                    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc678yx, htr258c, htr2810a, htr567a, htr568c, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                      linarith only [hlam, hc235yx, hc8910yz, htr125a, htr129a, htr236a, htr2910a, htr368a, htr6810a])
                    obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc679yx, htr259c, htr2910a, htr567a, htr569c, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd67b, hd89a, htr567a, htr569a, htr6910a, htr8910a]
                    ·
                      linarith only [hlam, hd67b, hd910a, htr567a, htr568a, htr689a, htr8910a]
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, htr046b, htr067a, htr467a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, htr246b, htr267a, htr467a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc234zy, htr246a, htr346b, htr367a, htr467a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            rcases m.htr 4 6 8 (by decide) (by decide) with
              ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc134zy, htr016c, htr068a, htr146c, htr346a, htr468a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, htr067c, htr068b, htr078c])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc234zy, htr246c, htr268a, htr346a, htr468a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hd45a, hd68b, htr047b, htr078a, htr267c, htr268a, htr278a, htr345a, htr347a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, htr346c, htr368a, htr468a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc245yx, hc789yx, htr125a, htr127a, htr246a, htr278a, htr467a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hc678xy, htr067c, htr068a, htr079a, htr679a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hd45a, hd68b, htr047b, htr079a, htr267c, htr268a, htr279a, htr345a, htr347a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                linarith only [hlam, hc245yx, hc7810yx, htr125a, htr127a, htr246a, htr278a, htr467a, htr6710a])
              obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, hc678xy, htr067c, htr068a, htr0710a, htr6710a])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                linarith only [hlam, hd45a, hd68b, htr047b, htr0710a, htr267c, htr268a, htr2710a, htr345a, htr347a])
              obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd45a, hd89b, htr345a, htr346a, htr468a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc678xy, htr367a, htr368b, htr389a, htr689a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd45a, hd910b, htr047b, htr079a, htr345a, htr347a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hd45a, hd79b, htr345a, htr349a, htr4910a, htr7910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc245yx, hc789zy, htr125a, htr127a, htr249a, htr279a, htr4910a, htr8910a]
              ·
                linarith only [hlam, hc235yx, hc7910zy, htr125a, htr127a, htr238a, htr2710a, htr389a, htr8910a]
            ·
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc234zy, htr247c, htr278a, htr347a, htr478a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, htr347c, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd45a, hd89b, htr345a, htr347a, htr478a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hd45a, hd78b, htr345a, htr348a, htr489a, htr789a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc245yx, hc678yz, htr125a, htr127a, htr248a, htr278a, htr489a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, hc245yx, hc789zy, htr125a, htr127a, htr246a, htr279a, htr468a, htr689a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hc245yx, hc8910xy, htr125a, htr128a, htr246a, htr2810a, htr468a, htr689a])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hd45a, hd78b, htr278a, htr279a, htr345a, htr347b, htr379a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                  linarith only [hlam, hc258xy, hc789yx, htr125a, htr127a, htr278a, htr2810a, htr378b, htr379a, htr3810a])
                obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc235yx, hc678yz, htr125a, htr127a, htr238a, htr278a, htr3810a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                  linarith only [hlam, hc245yx, hc8910yz, htr125a, htr129a, htr246a, htr2910a, htr468a, htr6810a])
                obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc789yx, htr278a, htr279c, htr2910a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd78b, hd89a, htr278a, htr279a, htr7910a, htr8910a]
                ·
                  linarith only [hlam, hd24b, hd910a, htr246a, htr468a, htr689a, htr8910a]
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr047b, htr078a, htr478a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, htr247b, htr278a, htr478a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc234zy, htr247a, htr347b, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                    linarith only [hlam, hc679xy, htr367c, htr369a, htr378a, htr678a])
                  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd24b, hd79a, htr247a, htr478a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  rcases m.htr 5 7 9 (by decide) (by decide) with
                    ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, htr057c, htr079a, htr579a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr078c, htr079b, htr089c])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hd45a, hd79b, htr048b, htr089a, htr257c, htr278c, htr289a, htr345a, htr348a, htr579a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, htr237b, htr257c, htr379a, htr579a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                    have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      linarith only [hlam, hc245yx, hc8910yx, htr125a, htr128a, htr247a, htr289a, htr478a, htr7810a])
                    obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc067zy, htr078c, htr0810a, htr678a, htr7810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                      linarith only [hlam, hd45a, hd79b, htr048b, htr0810a, htr257c, htr278c, htr2810a, htr345a, htr348a, htr579a])
                    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc235yx, hc8910zy, htr125a, htr128a, htr236a, htr2810a, htr369a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                      linarith only [hlam, hc013xy, hc679yz, htr015a, htr039a, htr157a, htr3910a, htr579a, htr6910a])
                    obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd45a, hd910b, htr048b, htr089a, htr345a, htr348a, htr8910a]
                    ·
                      linarith only [hlam, hd67a, hd89b, htr378a, htr379b, htr3910a, htr678a, htr8910a]
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, hc567zy, htr047b, htr079a, htr478a, htr579a, htr678a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, hc567zy, htr378a, htr379a, htr579a, htr678a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                    rcases m.htr 5 7 10 (by decide) (by decide) with
                      ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    ·
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, htr057c, htr0710a, htr5710a])
                      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, htr0710b, htr078c, htr0810c])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                        linarith only [hlam, htr0710b, htr079c, htr0910c])
                      obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                        linarith only [hlam, hd45a, hd710b, htr048b, htr0810a, htr257c, htr278c, htr2810a, htr345a, htr348a, htr5710a])
                      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hc245yx, hc8910xy, htr125a, htr128a, htr247a, htr2810a, htr478a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, hc067zy, htr078c, htr089a, htr678a, htr789a])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd45a, hd910b, htr048b, htr089a, htr345a, htr348a, htr8910a]
                      ·
                        linarith only [hlam, hd45a, hd89b, htr049b, htr0910a, htr345a, htr349a, htr8910a]
                    ·
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, hc067zy, htr078c, htr089a, htr678a, htr789a])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                          linarith only [hlam, hc267zy, htr278c, htr289a, htr678a, htr789a])
                        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc245yx, hc8910yx, htr125a, htr128a, htr247a, htr289a, htr478a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, hc067zy, htr078c, htr0810a, htr678a, htr7810a])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                          linarith only [hlam, hd45a, hd89b, htr048b, htr0810a, htr2810a, htr289a, htr345a, htr348a])
                        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hc235yx, hc8910zy, htr125a, htr128a, htr236a, htr2810a, htr369a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                          linarith only [hlam, hc235yx, hc689yz, htr125a, htr128a, htr239a, htr289a, htr3910a, htr6910a])
                        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                          linarith only [hlam, hc567zy, htr059c, htr0910a, htr379b, htr3910a, htr579c, htr679a])
                        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd45a, hd910b, htr048b, htr089a, htr345a, htr348a, htr8910a]
                        ·
                          linarith only [hlam, hd45a, hd89b, htr049b, htr0910a, htr345a, htr349a, htr8910a]
                      ·
                        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                          linarith only [hlam, hc245yx, hc8910xy, htr125a, htr128a, htr247a, htr2810a, htr478a, htr789a])
                        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                          linarith only [hlam, hc267zy, htr278c, htr2810a, htr378b, htr3810a, htr678a])
                        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hd24b, hd68a, htr247a, htr478a, htr689a, htr789a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                          linarith only [hlam, hd23b, hd89a, htr238a, htr3810a, htr6810a, htr689a])
                        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                          linarith only [hlam, hc245yx, hc8910yz, htr125a, htr129a, htr246a, htr2910a, htr468a, htr6810a])
                        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hc567zy, htr259c, htr2910a, htr579c, htr679a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd23b, hd89a, htr237a, htr379a, htr7910a, htr8910a]
                        ·
                          linarith only [hlam, hd24b, hd910a, htr247a, htr478a, htr789a, htr8910a]
                ·
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc245yx, hc789xy, htr125a, htr127a, htr246a, htr279a, htr467a, htr678a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                    linarith only [hlam, hc245yx, hc7810xy, htr125a, htr127a, htr246a, htr2710a, htr467a, htr678a])
                  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc234zy, htr247c, htr279a, htr347a, htr479a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc234zy, htr247c, htr2710a, htr347a, htr4710a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd24b, hd78a, htr247a, htr479a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc245yx, hc789yz, htr125a, htr128a, htr246a, htr289a, htr467a, htr679a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc234zy, htr248c, htr289a, htr348a, htr489a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd24b, hd78a, htr247a, htr4710a, htr6710a, htr678a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                    linarith only [hlam, hc245yx, hc7910yz, htr125a, htr129a, htr246a, htr2910a, htr467a, htr6710a])
                  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd24b, hd89a, htr246a, htr467a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd24b, hd910a, htr246a, htr467a, htr679a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc278zy, htr289c, htr2910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hd24b, hd79a, htr248a, htr489a, htr7910a, htr8910a]
        ·
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr3410c, htr346b, htr3610b])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr3410c, htr347b, htr3710b])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, htr3410c, htr348b, htr3810b])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, htr346c, htr3610a, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc6710yx, htr3410a, htr346a, htr4610b, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, htr347c, htr3710a, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc7810yx, htr3410a, htr347a, htr4710b, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, htr348c, htr3810a, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hd24b, hd67a, htr246a, htr3410a, htr346a, htr4710b, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd24b, hd710a, htr247a, htr478a, htr6710a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd24b, hd78a, htr246a, htr3410a, htr346a, htr4810b, htr7810a]
          ·
            linarith only [hlam, hd24b, hd810a, htr246a, htr467a, htr678a, htr7810a]
      ·
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr346b, htr349c, htr369b])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr347b, htr349c, htr379b])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, htr348b, htr349c, htr389b])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, htr346c, htr369a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc679yx, htr346a, htr349a, htr467a, htr469b])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, htr347c, htr379a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc789yx, htr347a, htr349a, htr478a, htr479b])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, htr348c, htr389a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr246a, htr346a, htr349a, htr479b, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd24b, hd79a, htr247a, htr478a, htr678a, htr679a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd24b, hd78a, htr246a, htr346a, htr349a, htr489b, htr789a]
        ·
          linarith only [hlam, hd24b, hd89a, htr246a, htr467a, htr678a, htr789a]
    ·
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr346b, htr348c, htr368b])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr347b, htr348c, htr378b])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr346c, htr368a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc678yx, htr346a, htr348a, htr467a, htr468b])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, htr347c, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc789xy, htr347a, htr348a, htr478b, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hc7810xy, htr347a, htr348a, htr4710a, htr478b])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd24b, hd89a, htr246a, htr346a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd24b, hd67a, htr246a, htr346a, htr348a, htr478b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd24b, hd78a, htr247a, htr479a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hc245yx, hc789yz, htr125a, htr128a, htr246a, htr289a, htr467a, htr679a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc248zy, htr289a, htr348a, htr349a, htr489c])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd24b, hd910a, htr246a, htr346a, htr349a, htr4910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        linarith only [hlam, hd24b, hd78a, htr247a, htr4710a, htr6710a, htr678a])
      obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
      have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
        linarith only [hlam, hc245yx, hc7910yz, htr125a, htr129a, htr246a, htr2910a, htr467a, htr6710a])
      obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc248zy, htr289c, htr2910a, htr489a, htr8910a]
      ·
        linarith only [hlam, hc248zy, htr289a, htr489b, htr4910a, htr8910a]
  ·
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr346b, htr347c, htr367b])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, htr346c, htr367a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc678xy, htr346a, htr347a, htr467b, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hc679xy, htr346a, htr347a, htr467b, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd24b, hd78a, htr246a, htr346a, htr347a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd24b, hd79a, htr246a, htr346a, htr347a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    rcases m.htr 5 7 8 (by decide) (by decide) with
      ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
    ·
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc014xy, hc478yz, htr015a, htr046a, htr157a, htr346a, htr348a, htr578a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr015a, htr157a, htr578a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd45a, hd78b, htr345a, htr348a, htr489a, htr789a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc014xy, hc678yz, htr015a, htr048a, htr157a, htr489a, htr578a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc245yx, hc789zy, htr125a, htr127a, htr246a, htr279a, htr468a, htr689a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
        linarith only [hlam, hc245yx, hc8910xy, htr125a, htr128a, htr246a, htr2810a, htr468a, htr689a])
      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc247zy, htr279a, htr347a, htr349a, htr479c])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hc234zy, htr248c, htr2810a, htr348a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd24b, hd910a, htr246a, htr346a, htr349a, htr4910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hc014xy, hc678yz, htr015a, htr048a, htr157a, htr4810a, htr578a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
        linarith only [hlam, hc245yx, hc8910yz, htr125a, htr129a, htr246a, htr2910a, htr468a, htr6810a])
      obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
      rcases m.htr 7 9 10 (by decide) (by decide) with
        ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      ·
        linarith only [hlam, hc247zy, htr279c, htr2910a, htr479a, htr7910a]
      ·
        linarith only [hlam, hc247zy, htr279a, htr479b, htr4910a, htr7910a]
    ·
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc457yz, htr347a, htr348a, htr478c, htr578a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd24b, hd89a, htr246a, htr346a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hd24b, hd810a, htr246a, htr346a, htr348a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc457yz, htr478b, htr489a, htr578a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hc457yz, htr258c, htr289a, htr478a, htr578c, htr789a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc245yx, hc489yz, htr125a, htr128a, htr246a, htr289a, htr346a, htr349a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        linarith only [hlam, hc457yz, htr478b, htr4810a, htr578a, htr7810a])
      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
        linarith only [hlam, hc457yz, htr258c, htr2810a, htr478a, htr578c, htr7810a])
      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc245yx, hc8910zy, htr125a, htr128a, htr246a, htr2810a, htr469a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hc245yx, hc689yz, htr125a, htr128a, htr249a, htr289a, htr4910a, htr6910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hd01a, hd910b, htr012a, htr128a, htr289a, htr8910a]
      ·
        linarith only [hlam, hd45a, hd89b, htr345a, htr349a, htr4910a, htr8910a]

theorem shard_033 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr039a : m.d 3 9 + lam ≤ m.d 0 3)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr048a : m.d 4 8 + lam ≤ m.d 0 4)
    (htr048b : m.d 4 8 < m.d 0 8)
    (htr049b : m.d 4 9 < m.d 0 9)
    (htr057c : m.d 0 7 < m.d 5 7)
    (htr058c : m.d 0 8 < m.d 5 8)
    (htr059c : m.d 0 9 < m.d 5 9)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr156a : m.d 1 5 + lam ≤ m.d 5 6)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr158a : m.d 1 5 + lam ≤ m.d 5 8)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr239a : m.d 3 9 + lam ≤ m.d 2 3)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246b : m.d 4 6 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr248c : m.d 2 8 < m.d 2 4)
    (htr249a : m.d 4 9 + lam ≤ m.d 2 4)
    (htr256c : m.d 2 6 < m.d 5 6)
    (htr257c : m.d 2 7 < m.d 5 7)
    (htr258c : m.d 2 8 < m.d 5 8)
    (htr259c : m.d 2 9 < m.d 5 9)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    : False :=
  proof_shard_033 m htr012a htr015a htr016c htr036a htr039a htr046a htr046b htr047b htr048a htr048b htr049b htr057c htr058c htr059c htr125a htr126a htr127a htr128a htr129a htr136b htr146c htr156a htr156c htr157a htr158a htr236a htr237a htr237b htr238a htr239a htr246a htr246b htr246c htr247a htr247b htr247c htr248a htr248c htr249a htr256c htr257c htr258c htr259c htr345a htr346a htr346b htr346c

#print axioms shard_033
end Jsp404.NoSatElevenDBMTerminal
