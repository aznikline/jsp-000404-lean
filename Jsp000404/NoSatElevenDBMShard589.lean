import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_589 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr156b : m.d 5 6 < m.d 1 6)
    (htr157a : m.d 5 7 + lam ≤ m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr248a : m.d 2 4 + lam ≤ m.d 4 8)
    (htr249a : m.d 2 4 + lam ≤ m.d 4 9)
    (htr2410a : m.d 2 4 + lam ≤ m.d 4 10)
    (htr256b : m.d 5 6 < m.d 2 6)
    (htr257b : m.d 5 7 < m.d 2 7)
    (htr258b : m.d 5 8 < m.d 2 8)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
  have hd26a := (m.hrange 2 6 (by decide)).1
  have hd28a := (m.hrange 2 8 (by decide)).1
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd49a, hd49braw⟩ := m.hrange 4 9 (by decide)
  have hd49b : m.d 4 9 < 4*lam := by
    linarith only [hd49braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  have hd69a := (m.hrange 6 9 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
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
  obtain ⟨hc046xy, hc046yx, hc046yz, hc046zy⟩ := endpoint_caps m 0 4 6 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc258xy, hc258yx, hc258yz, hc258zy⟩ := endpoint_caps m 2 5 8 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc479xy, hc479yx, hc479yz, hc479zy⟩ := endpoint_caps m 4 7 9 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
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
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr267a, htr567a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc256yx, htr025a, htr026c, htr067a, htr267a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc235xy, hc678yx, htr125a, htr126a, htr234a, htr268a, htr346a, htr467a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hc235xy, hc679yx, htr125a, htr126a, htr234a, htr269a, htr346a, htr467a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd23a, hd79b, htr234a, htr346a, htr467a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc567yz, htr467a, htr468a, htr578a, htr678b])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hd23a, hd810b, htr234a, htr346a, htr468a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hc567yz, htr258b, htr289a, htr578b, htr678a, htr789a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                  linarith only [hlam, hc235xy, hc689zy, htr125a, htr128a, htr234a, htr289a, htr346a, htr469a])
                obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  linarith only [hlam, hc567yz, htr578a, htr678c, htr6810a, htr7810a])
                obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hc567yz, htr258b, htr2810a, htr578b, htr678a, htr7810a])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc235xy, hc8910yz, htr125a, htr128a, htr234a, htr2810a, htr349a, htr4910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hc256yx, hc489zy, htr125a, htr128a, htr269a, htr289a, htr4910a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd67b, hd89a, htr467a, htr469a, htr6910a, htr8910a]
                ·
                  linarith only [hlam, hd01b, hd910a, htr012a, htr128a, htr289a, htr8910a]
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc013yx, hc678zy, htr015a, htr034a, htr157a, htr346a, htr468a, htr578a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd23a, hd67b, htr236a, htr368a, htr467a, htr468a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd01b, hd89a, htr015a, htr157a, htr578a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd67b, hd78a, htr467a, htr468a, htr689a, htr789a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc256yx, hc478zy, htr125a, htr127a, htr257b, htr268a, htr489a, htr578a, htr689a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, hc235xy, hc789yz, htr125a, htr127a, htr234a, htr279a, htr348a, htr489a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hc235xy, hc8910yx, htr125a, htr128a, htr234a, htr2810a, htr348a, htr489a])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                  linarith only [hlam, hc267yz, htr279a, htr346c, htr369a, htr467a, htr679b])
                obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hd28a, hd67b, htr2810a, htr467a, htr468a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc256yx, hc478zy, htr125a, htr127a, htr257b, htr268a, htr4810a, htr578a, htr6810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                  linarith only [hlam, hc235xy, hc8910zy, htr125a, htr129a, htr234a, htr2910a, htr348a, htr4810a])
                obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd26a, hd910b, htr268a, htr368a, htr369a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc267yz, htr279a, htr679c, htr6910a, htr7910a]
                ·
                  linarith only [hlam, hc267yz, htr279b, htr2910a, htr679a, htr7910a]
            ·
              rcases m.htr 3 6 7 (by decide) (by decide) with
                ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hd23a, hd68b, htr236a, htr367a, htr467a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                rcases m.htr 5 6 8 (by decide) (by decide) with
                  ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc456zy, htr067a, htr068a, htr467a, htr568a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hc456zy, htr367a, htr368a, htr467a, htr568a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  rcases m.htr 5 6 9 (by decide) (by decide) with
                    ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
                  ·
                    rcases m.htr 5 6 10 (by decide) (by decide) with
                      ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                    ·
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc235xy, hc789yx, htr125a, htr127a, htr236a, htr279a, htr367a, htr678a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc456zy, htr257b, htr279a, htr367c, htr379a, htr467a, htr567b])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hd23a, hd78b, htr237a, htr379a, htr478a, htr479a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                          linarith only [hlam, hc235xy, hc789zy, htr125a, htr128a, htr234a, htr289a, htr347a, htr479a])
                        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc456zy, htr258b, htr289a, htr468a, htr568b, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd23a, hd89b, htr236a, htr367a, htr678a, htr789a]
                        ·
                          linarith only [hlam, hd23a, hd78b, htr236a, htr368a, htr689a, htr789a]
                      ·
                        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                          linarith only [hlam, hc456zy, htr257b, htr278a, htr467a, htr567b, htr678a])
                        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                          linarith only [hlam, hc235xy, hc789xy, htr125a, htr127a, htr236a, htr278a, htr367a, htr679a])
                        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc456zy, htr257b, htr279a, htr467a, htr567b, htr679a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc235xy, hc789yz, htr125a, htr127a, htr234a, htr279a, htr348a, htr489a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                          linarith only [hlam, hc235xy, hc478zy, htr125a, htr127a, htr238a, htr278a, htr389a, htr489a])
                        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                          linarith only [hlam, hc456zy, htr258b, htr289a, htr368c, htr389a, htr468a, htr568b])
                        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
                        ·
                          linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
                    ·
                      have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                        linarith only [hlam, htr016b, htr0610a, htr156b, htr5610a])
                      obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, htr0610c, htr067b, htr0710b])
                      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, htr0610c, htr068b, htr0810b])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                        linarith only [hlam, hc257yx, htr025a, htr027c, htr0710a, htr2710a])
                      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                        linarith only [hlam, hc258yx, htr025a, htr028c, htr0810a, htr2810a])
                      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc235xy, hc7810yx, htr125a, htr127a, htr236a, htr2710a, htr367a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                        linarith only [hlam, hc456zy, htr257b, htr278a, htr467a, htr567b, htr678a])
                      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                      rcases m.htr 7 8 10 (by decide) (by decide) with
                        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      ·
                        linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr2810a, htr7810a]
                      ·
                        linarith only [hlam, hd01b, hd810a, htr012a, htr127a, htr278a, htr7810a]
                  ·
                    have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                      linarith only [hlam, htr016b, htr069a, htr156b, htr569a])
                    obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, htr067b, htr069c, htr079b])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr068b, htr069c, htr089b])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, hc257yx, htr025a, htr027c, htr079a, htr279a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hc258yx, htr025a, htr028c, htr089a, htr289a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc235xy, hc789yx, htr125a, htr127a, htr236a, htr279a, htr367a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc456zy, htr257b, htr278a, htr467a, htr567b, htr678a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
                    ·
                      linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, htr016b, htr068a, htr156b, htr568a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, htr067b, htr068c, htr078b])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc257yx, htr025a, htr027c, htr078a, htr278a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, htr136c, htr156b, htr368a, htr568a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc235xy, hc789xy, htr125a, htr127a, htr236a, htr278a, htr367a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc456zy, htr257b, htr279a, htr467a, htr567b, htr679a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc235xy, hc789yz, htr125a, htr127a, htr234a, htr279a, htr348a, htr489a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                    linarith only [hlam, hc235xy, hc468zy, htr125a, htr126a, htr238a, htr256b, htr389a, htr489a, htr568a])
                  obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd46b, hd78a, htr367a, htr368c, htr389a, htr467a, htr789a]
                  ·
                    linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
              ·
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc235xy, hc789yx, htr125a, htr127a, htr234a, htr279a, htr347a, htr478a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                    linarith only [hlam, hc235xy, hc7810yx, htr125a, htr127a, htr234a, htr2710a, htr347a, htr478a])
                  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456zy, htr257b, htr279a, htr467a, htr567b, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc235xy, hc789zy, htr125a, htr128a, htr234a, htr289a, htr347a, htr479a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hc456zy, htr257b, htr2710a, htr467a, htr567b, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr4710a, htr567a, htr6710a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                    linarith only [hlam, hc235xy, hc7910zy, htr125a, htr129a, htr234a, htr2910a, htr347a, htr4710a])
                  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd23a, hd910b, htr234a, htr347a, htr479a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc278yz, htr289a, htr789c, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hc278yz, htr289b, htr2910a, htr789a, htr8910a]
                ·
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc456zy, htr257b, htr278a, htr467a, htr567b, htr678a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc235xy, hc789xy, htr125a, htr127a, htr234a, htr278a, htr347a, htr479a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc235xy, hc7810xy, htr125a, htr127a, htr234a, htr278a, htr347a, htr4710a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc456zy, htr257b, htr279a, htr467a, htr567b, htr679a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc235xy, hc789yz, htr125a, htr127a, htr234a, htr279a, htr348a, htr489a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr4710a, htr567a, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                    linarith only [hlam, hc456zy, htr257b, htr2710a, htr467a, htr567b, htr6710a])
                  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc235xy, hc7910yz, htr125a, htr127a, htr234a, htr2710a, htr349a, htr4910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
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
                    linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hc478zy, htr489a, htr789b, htr7910a, htr8910a]
          ·
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc235xy, hc678xy, htr125a, htr126a, htr234a, htr256b, htr346a, htr468a, htr567a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd01b, hd78a, htr015a, htr156a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hd01b, hd79a, htr015a, htr156a, htr567a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr279a, htr679a])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd25b, hd67a, htr025a, htr026c, htr068a, htr567a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc467zy, htr478a, htr567a, htr568a, htr678c])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd67a, hd78b, htr567a, htr568a, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc678xy, htr258b, htr289a, htr567a, htr568b, htr689a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc235xy, hc789zy, htr125a, htr128a, htr234a, htr289a, htr347a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc467zy, htr016b, htr069a, htr156b, htr479a, htr567a, htr679c])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc8910xy, htr068a, htr069a, htr6810a, htr689b])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                linarith only [hlam, hc678xy, htr258b, htr2810a, htr567a, htr568b, htr6810a])
              obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc235xy, hc8910yz, htr125a, htr128a, htr234a, htr2810a, htr349a, htr4910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd46b, hd910a, htr068a, htr069a, htr468a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc257yx, hc489zy, htr125a, htr128a, htr279a, htr289a, htr4910a, htr7910a]
              ·
                linarith only [hlam, hc467zy, htr479a, htr679b, htr6910a, htr7910a]
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc235xy, hc678yz, htr125a, htr126a, htr234a, htr256b, htr347a, htr478a, htr568a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd01b, hd89a, htr015a, htr156a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd01b, hd810a, htr015a, htr156a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc257yx, hc468zy, htr125a, htr126a, htr256b, htr278a, htr489a, htr568a, htr789a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hc235xy, hc689yz, htr125a, htr126a, htr234a, htr269a, htr348a, htr489a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc467zy, htr478a, htr678b, htr6810a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hc257yx, hc468zy, htr125a, htr126a, htr256b, htr278a, htr4810a, htr568a, htr7810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                linarith only [hlam, hc235xy, hc8910zy, htr125a, htr129a, htr234a, htr2910a, htr348a, htr4810a])
              obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc679xy, htr256b, htr269b, htr2910a, htr567a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
              ·
                linarith only [hlam, hd67a, hd89b, htr256b, htr269a, htr567a, htr6910a, htr8910a]
        ·
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc245xy, hc467zy, htr125a, htr126a, htr2410a, htr267a, htr3410a, htr347a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc256yx, htr025a, htr026c, htr067a, htr267a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc245xy, hc478zy, htr125a, htr127a, htr2410a, htr278a, htr3410a, htr348a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr3410c, htr346b, htr3610b])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd24a, hd67b, htr2410a, htr3410a, htr346a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, htr346c, htr3610a, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
            linarith only [hlam, hc046yz, htr0610a, htr3410a, htr346a, htr4610b])
          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0610c, htr067b, htr0710b])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
            linarith only [hlam, hc257yx, htr025a, htr027c, htr0710a, htr2710a])
          obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc245xy, hc7810yx, htr125a, htr127a, htr2410a, htr2710a, htr3410a, htr347b, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hc246yz, htr267a, htr347c, htr378a, htr467c, htr678a]
          ·
            linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a]
      ·
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc245xy, hc467zy, htr125a, htr126a, htr249a, htr267a, htr347a, htr349a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc256yx, htr025a, htr026c, htr067a, htr267a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc245xy, hc478zy, htr125a, htr127a, htr249a, htr278a, htr348a, htr349a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr346b, htr349c, htr369b])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd24a, hd67b, htr249a, htr346a, htr349a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, htr346c, htr369a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, hc046yz, htr069a, htr346a, htr349a, htr469b])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr067b, htr069c, htr079b])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc257yx, htr025a, htr027c, htr079a, htr279a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc245xy, hc789yx, htr125a, htr127a, htr249a, htr279a, htr347b, htr349a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hc246yz, htr267a, htr347c, htr378a, htr467c, htr678a]
        ·
          linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a]
    ·
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc245xy, hc467zy, htr125a, htr126a, htr248a, htr267a, htr347a, htr348a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc256yx, htr025a, htr026c, htr067a, htr267a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr346b, htr348c, htr368b])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd24a, hd67b, htr248a, htr346a, htr348a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc468yx, htr346b, htr348a, htr367a, htr467a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr346c, htr368a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc046yz, htr068a, htr346a, htr348a, htr468b])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr067b, htr068c, htr078b])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc257yx, htr025a, htr027c, htr078a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hc689xy, htr067a, htr068a, htr367a, htr369a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hc245xy, hc789xy, htr125a, htr127a, htr248a, htr278a, htr347b, htr348a, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
        linarith only [hlam, hc245xy, hc7810xy, htr125a, htr127a, htr248a, htr278a, htr347b, htr348a, htr3710a])
      obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, htr346c, htr369a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc246yz, htr267a, htr347c, htr379a, htr467c, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc246yz, htr267b, htr279a, htr467a, htr679a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc245xy, hc479zy, htr125a, htr127a, htr248a, htr279a, htr348a, htr349a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc046yz, htr069a, htr346a, htr349a, htr469b])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        linarith only [hlam, hc246yz, htr267a, htr347c, htr3710a, htr467c, htr6710a])
      obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hc246yz, htr267b, htr2710a, htr467a, htr6710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd46b, hd89a, htr067a, htr068a, htr467a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd45b, hd68a, htr345a, htr348a, htr489a, htr689a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd46b, hd910a, htr067a, htr069a, htr467a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd45b, hd69a, htr345a, htr349a, htr4910a, htr6910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc245xy, hc7910yz, htr125a, htr127a, htr248a, htr2710a, htr489a, htr8910a]
      ·
        linarith only [hlam, hc245xy, hc789yz, htr125a, htr127a, htr249a, htr279a, htr4910a, htr8910a]
  ·
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr346b, htr347c, htr367b])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, htr346c, htr367a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc246yz, htr267a, htr346a, htr347a, htr467b])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc245xy, hc678xy, htr125a, htr126a, htr247a, htr267a, htr346b, htr347a, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hc245xy, hc679xy, htr125a, htr126a, htr247a, htr267a, htr346b, htr347a, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, htr346c, htr368a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, htr346c, htr369a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd01b, hd79a, htr012a, htr126a, htr267a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr479a, htr679a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    rcases m.htr 5 6 8 (by decide) (by decide) with
      ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
    ·
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc245xy, hc456zy, htr025a, htr026c, htr068a, htr247a, htr346a, htr347a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc456zy, htr346a, htr348a, htr468b, htr568a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd24a, hd89b, htr247a, htr347a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hd24a, hd810b, htr247a, htr347a, htr348a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hc356zy, htr258b, htr289a, htr368a, htr568b, htr689a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc245xy, hc489zy, htr125a, htr128a, htr247a, htr289a, htr347a, htr349a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc046yz, htr069a, htr346a, htr349a, htr469b])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hc456zy, htr468c, htr4810a, htr568a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
        linarith only [hlam, hc356zy, htr258b, htr2810a, htr368a, htr568b, htr6810a])
      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd36b, hd910a, htr068a, htr069a, htr368a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd45b, hd69a, htr345a, htr349a, htr4910a, htr6910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      rcases m.htr 7 9 10 (by decide) (by decide) with
        ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      ·
        linarith only [hlam, hc245xy, hc8910yz, htr125a, htr128a, htr247a, htr2810a, htr479a, htr7910a]
      ·
        linarith only [hlam, hc245xy, hc789zy, htr125a, htr128a, htr249a, htr289a, htr4910a, htr7910a]
    ·
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc245xy, hc468zy, htr125a, htr126a, htr247a, htr256b, htr347a, htr348a, htr568a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr015a, htr156a, htr568a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd45b, hd68a, htr345a, htr348a, htr489a, htr689a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hd01b, hd810a, htr015a, htr156a, htr568a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hd45b, hd68a, htr345a, htr348a, htr4810a, htr6810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc245xy, hc678yz, htr125a, htr126a, htr248a, htr256b, htr489a, htr568a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hc245xy, hc689yz, htr125a, htr126a, htr247a, htr269a, htr478a, htr789a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc246yz, htr269a, htr346a, htr349a, htr469b])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd24a, hd910b, htr247a, htr347a, htr349a, htr4910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd49b, hd67a, htr267a, htr269a, htr4910a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
        linarith only [hlam, hc679xy, htr267a, htr269b, htr2910a, htr6910a])
      obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
      rcases m.htr 7 8 10 (by decide) (by decide) with
        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
      ·
        linarith only [hlam, hc245xy, hc8910zy, htr125a, htr129a, htr247a, htr2910a, htr478a, htr7810a]
      ·
        linarith only [hlam, hc245xy, hc678yz, htr125a, htr126a, htr248a, htr256b, htr4810a, htr568a, htr7810a]

theorem shard_589 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr156b : m.d 5 6 < m.d 1 6)
    (htr157a : m.d 5 7 + lam ≤ m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr248a : m.d 2 4 + lam ≤ m.d 4 8)
    (htr249a : m.d 2 4 + lam ≤ m.d 4 9)
    (htr2410a : m.d 2 4 + lam ≤ m.d 4 10)
    (htr256b : m.d 5 6 < m.d 2 6)
    (htr257b : m.d 5 7 < m.d 2 7)
    (htr258b : m.d 5 8 < m.d 2 8)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    : False :=
  proof_shard_589 m htr012a htr015a htr016b htr025a htr026c htr027c htr028c htr034a htr125a htr126a htr127a htr128a htr129a htr136c htr156a htr156b htr157a htr234a htr236a htr237a htr238a htr247a htr248a htr249a htr2410a htr256b htr257b htr258b htr345a htr346a htr346b htr346c

#print axioms shard_589
end Jsp404.NoSatElevenDBMTerminal
