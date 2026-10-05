import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_551 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
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
  have hd79a := (m.hrange 7 9 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc018xy, hc018yx, hc018yz, hc018zy⟩ := endpoint_caps m 0 1 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, htr345c, htr356a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd01b, hd67a, htr013a, htr135a, htr356a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr267a, htr567a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd01b, hd68a, htr013a, htr135a, htr356a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr268a, htr568a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, hc236yx, htr023a, htr026c, htr068a, htr268a])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, htr046b, htr048c, htr068b])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hd01b, hd69a, htr013a, htr135a, htr356a, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr269a, htr569a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  rcases m.htr 3 5 7 (by decide) (by decide) with
    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hd23b, hd56a, htr023a, htr025c, htr057a, htr356a, htr357a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc456zy, htr356a, htr357a, htr467a, htr567c])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc567xy, htr456c, htr457a, htr468a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      rcases m.htr 4 5 8 (by decide) (by decide) with
        ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr045c, htr058a, htr458a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc234yx, htr123a, htr125a, htr245a, htr258a, htr458a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 4 5 9 (by decide) (by decide) with
          ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
        ·
          rcases m.htr 4 5 10 (by decide) (by decide) with
            ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
          ·
            rcases m.htr 3 7 8 (by decide) (by decide) with
              ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
            ·
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc567xy, htr356a, htr357b, htr378a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hc234yx, hc789yx, htr123a, htr127a, htr245a, htr279a, htr457a, htr578a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc567xy, htr237b, htr279a, htr356a, htr357b, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc234yx, hc789zy, htr123a, htr128a, htr245a, htr289a, htr457a, htr579a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568xy, htr235b, htr258b, htr289a, htr356a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd56a, hd89b, htr356a, htr357a, htr578a, htr789a]
              ·
                linarith only [hlam, hd34a, hd78b, htr345a, htr458a, htr589a, htr789a]
            ·
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc234yx, hc789xy, htr123a, htr127a, htr237b, htr245a, htr378a, htr457a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hc567xy, htr237b, htr279a, htr356a, htr357b, htr579a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc234yx, hc789yz, htr123a, htr127a, htr245a, htr279a, htr458a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc568xy, htr235b, htr258b, htr289a, htr356a, htr589a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
              ·
                linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a]
          ·
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, hc567xy, htr035b, htr0510a, htr356a, htr4510a, htr457a])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0510c, htr057b, htr0710b])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
              linarith only [hlam, htr0510c, htr058b, htr0810b])
            obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, hc237yx, htr023a, htr027c, htr0710a, htr2710a])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
              linarith only [hlam, hc238yx, htr023a, htr028c, htr0810a, htr2810a])
            obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc234yx, hc7810yx, htr123a, htr127a, htr245a, htr2710a, htr457a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc567xy, htr237b, htr278a, htr356a, htr357b, htr578a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            rcases m.htr 7 8 10 (by decide) (by decide) with
              ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            ·
              linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr2810a, htr7810a]
            ·
              linarith only [hlam, hd01b, hd810a, htr012a, htr127a, htr278a, htr7810a]
        ·
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, hc567xy, htr035b, htr059a, htr356a, htr457a, htr459a])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr057b, htr059c, htr079b])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
            linarith only [hlam, htr058b, htr059c, htr089b])
          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hc237yx, htr023a, htr027c, htr079a, htr279a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
            linarith only [hlam, hc238yx, htr023a, htr028c, htr089a, htr289a])
          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc234yx, hc789yx, htr123a, htr127a, htr245a, htr279a, htr457a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc567xy, htr237b, htr278a, htr356a, htr357b, htr578a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
          ·
            linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc567xy, htr035b, htr058a, htr356a, htr457a, htr458a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr057b, htr058c, htr078b])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc567xy, htr235b, htr258a, htr356a, htr457a, htr458a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc237yx, htr023a, htr027c, htr078a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc234yx, hc789xy, htr123a, htr127a, htr245a, htr278a, htr457a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc567xy, htr237b, htr279a, htr356a, htr357b, htr579a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc578yx, htr457a, htr458c, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc234yx, hc789yz, htr123a, htr127a, htr246a, htr279a, htr468a, htr689a]
        ·
          linarith only [hlam, hc014yx, hc568yz, htr012a, htr048a, htr125a, htr258a, htr489a, htr689a]
    ·
      rcases m.htr 3 5 8 (by decide) (by decide) with
        ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc567xy, htr057a, htr058a, htr356a, htr358a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc456zy, htr356a, htr358a, htr468a, htr568c])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        rcases m.htr 3 5 9 (by decide) (by decide) with
          ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
        ·
          rcases m.htr 3 5 10 (by decide) (by decide) with
            ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
          ·
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hd47b, hd56a, htr356a, htr357a, htr478a, htr578a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd56a, hd67b, htr356a, htr357a, htr578a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hc234yx, hc789yx, htr123a, htr127a, htr246a, htr279a, htr467a, htr678a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hd56a, hd78b, htr237b, htr279a, htr356a, htr357b, htr478a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd56a, hd78b, htr356a, htr357a, htr457b, htr479a, htr678a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc234yx, hc789zy, htr123a, htr128a, htr246a, htr289a, htr467a, htr679a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568xy, htr238b, htr289a, htr356a, htr358b, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd56a, hd89b, htr356a, htr357a, htr578a, htr789a]
              ·
                linarith only [hlam, hd56a, hd78b, htr356a, htr358a, htr589a, htr789a]
            ·
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc567xy, htr237b, htr278a, htr356a, htr357b, htr578a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc234yx, hc789xy, htr123a, htr127a, htr246a, htr278a, htr467a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd56a, hd67b, htr356a, htr357a, htr579a, htr679a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hc567xy, htr237b, htr279a, htr356a, htr357b, htr579a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc234yx, hc789yz, htr123a, htr127a, htr246a, htr279a, htr468a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hd56a, hd68b, htr356a, htr358a, htr589a, htr689a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc568xy, htr238b, htr289a, htr356a, htr358b, htr589a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
              ·
                linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
          ·
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, htr035b, htr0510a, htr3510a])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0510c, htr057b, htr0710b])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
              linarith only [hlam, htr0510c, htr058b, htr0810b])
            obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
            have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
              linarith only [hlam, hc238yx, htr023a, htr028c, htr0810a, htr2810a])
            obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
            have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
              linarith only [hlam, htr057c, htr0710a, htr5710a])
            obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc7810yx, htr035b, htr057a, htr3510a, htr5710b, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc567xy, htr237b, htr278a, htr356a, htr357b, htr578a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            rcases m.htr 7 8 10 (by decide) (by decide) with
              ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            ·
              linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr2810a, htr7810a]
            ·
              linarith only [hlam, hd01b, hd810a, htr012a, htr127a, htr278a, htr7810a]
        ·
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr035b, htr059a, htr359a])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr057b, htr059c, htr079b])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
            linarith only [hlam, htr058b, htr059c, htr089b])
          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
            linarith only [hlam, hc238yx, htr023a, htr028c, htr089a, htr289a])
          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, htr057c, htr079a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc789yx, htr035b, htr057a, htr359a, htr578a, htr579b])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc567xy, htr237b, htr278a, htr356a, htr357b, htr578a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
          ·
            linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr035b, htr058a, htr358a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr057b, htr058c, htr078b])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, htr057c, htr078a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc789xy, htr035b, htr057a, htr358a, htr578b, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc567xy, htr237b, htr279a, htr356a, htr357b, htr579a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
          linarith only [hlam, hc7810xy, htr035b, htr057a, htr358a, htr5710a, htr578b])
        obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
        have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
          linarith only [hlam, hc567xy, htr237b, htr2710a, htr356a, htr357b, htr5710a])
        obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr013a, htr135a, htr358a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, hc578yx, htr057a, htr058c, htr089a, htr589a])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, htr578b, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd01b, hd910a, htr012a, htr127a, htr279a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc236yx, hc7910yz, htr123a, htr127a, htr268a, htr2710a, htr689a, htr8910a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
            linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a])
          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hc236yx, hc568yz, htr123a, htr125a, htr235b, htr269a, htr358a, htr468a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          rcases m.htr 6 9 10 (by decide) (by decide) with
            ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          ·
            linarith only [hlam, hc234yx, hc7910yz, htr123a, htr127a, htr246a, htr2710a, htr469a, htr6910a]
          ·
            linarith only [hlam, hc018yx, hc679zy, htr012a, htr089a, htr127a, htr279a, htr6910a, htr8910a]
        ·
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
            linarith only [hlam, hc234yx, hc789yz, htr123a, htr127a, htr246a, htr279a, htr468a, htr689a])
          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hc236yx, hc679zy, htr123a, htr127a, htr268a, htr279a, htr468a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          rcases m.htr 6 9 10 (by decide) (by decide) with
            ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          ·
            linarith only [hlam, hc236yx, hc789yz, htr123a, htr127a, htr269a, htr279a, htr6910a, htr8910a]
          ·
            linarith only [hlam, hd67b, hd79a, htr467a, htr469a, htr6910a, htr7910a]
  ·
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd01b, hd79a, htr013a, htr135a, htr357a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr279a, htr579a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    rcases m.htr 4 6 7 (by decide) (by decide) with
      ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
    ·
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc236yx, hc567yz, htr123a, htr125a, htr235b, htr268a, htr357a, htr467a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc236yx, hc567yz, htr123a, htr125a, htr235b, htr269a, htr357a, htr467a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc234yx, hc578yz, htr123a, htr125a, htr246a, htr258a, htr467a, htr678a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc235yx, htr023a, htr025c, htr058a, htr258a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd34a, hd89b, htr346a, htr467a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd56a, hd78b, htr235b, htr258a, htr356a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc568xy, htr235b, htr258b, htr289a, htr356a, htr589a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc234yx, hc789zy, htr123a, htr128a, htr246a, htr289a, htr467a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc567yz, htr035b, htr059a, htr357a, htr579c, htr679a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr259a, htr259b, htr259c, _, _⟩
          linarith only [hlam, hc568xy, htr058a, htr059a, htr235b, htr259a, htr356a])
        obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc8910xy, htr058a, htr059a, htr5810a, htr589b])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc568xy, htr235b, htr258b, htr2810a, htr356a, htr5810a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd01b, hd910a, htr012a, htr125a, htr259a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc234yx, hc8910yz, htr123a, htr128a, htr246a, htr2810a, htr469a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc237yx, hc689zy, htr123a, htr128a, htr279a, htr289a, htr6910a, htr7910a]
        ·
          linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a]
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc567yz, htr235b, htr258a, htr357a, htr578c, htr678a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd01b, hd810a, htr012a, htr125a, htr258a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr259a, htr259b, htr259c, _, _⟩
          linarith only [hlam, hc234yx, hc589yz, htr123a, htr125a, htr246a, htr259a, htr468a, htr689a])
        obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc567yz, htr578b, htr5810a, htr678a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc567yz, htr578a, htr678c, htr6810a, htr7810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, hc234yx, hc8910zy, htr123a, htr129a, htr246a, htr2910a, htr468a, htr6810a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc569xy, htr235b, htr259b, htr2910a, htr356a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd34a, hd910b, htr346a, htr468a, htr689a, htr8910a]
        ·
          linarith only [hlam, hd56a, hd89b, htr235b, htr259a, htr356a, htr5910a, htr8910a]
    ·
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc568xy, htr456c, htr458a, htr467a, htr567a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc456zy, htr467a, htr567b, htr579a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      rcases m.htr 4 6 8 (by decide) (by decide) with
        ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc236yx, hc568yz, htr123a, htr125a, htr258a, htr267a, htr467a, htr468a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc235yx, htr023a, htr025c, htr058a, htr258a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd56a, hd89b, htr467a, htr468a, htr567a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd56a, hd68b, htr235b, htr258a, htr356a, htr589a, htr689a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc568xy, htr235b, htr258b, htr289a, htr356a, htr589a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc236yx, hc689zy, htr123a, htr128a, htr267a, htr289a, htr467a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc456zy, htr035b, htr059a, htr356a, htr469a, htr569c])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc8910xy, htr058a, htr059a, htr5810a, htr589b])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc568xy, htr235b, htr258b, htr2810a, htr356a, htr5810a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd45b, hd910a, htr058a, htr059a, htr458a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc456zy, htr469a, htr569b, htr5910a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc236yx, hc8910yz, htr123a, htr128a, htr267a, htr2810a, htr679a, htr7910a]
        ·
          linarith only [hlam, hc236yx, hc789zy, htr123a, htr128a, htr269a, htr289a, htr6910a, htr7910a]
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc456zy, htr235b, htr258a, htr356a, htr468a, htr568c])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd01b, hd810a, htr012a, htr125a, htr258a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc456zy, htr468a, htr568b, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc236yx, hc578yz, htr123a, htr125a, htr258a, htr268a, htr689a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr259a, htr259b, htr259c, _, _⟩
          linarith only [hlam, hc236yx, hc589yz, htr123a, htr125a, htr259a, htr267a, htr678a, htr789a])
        obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc456zy, htr235b, htr259a, htr356a, htr469a, htr569c])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd56a, hd910b, htr467a, htr469a, htr567a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd56a, hd69b, htr235b, htr259a, htr356a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, hc569xy, htr235b, htr259b, htr2910a, htr356a, htr5910a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc236yx, hc8910zy, htr123a, htr129a, htr267a, htr2910a, htr678a, htr7810a]
        ·
          linarith only [hlam, hc236yx, hc578yz, htr123a, htr125a, htr258a, htr268a, htr6810a, htr7810a]

theorem shard_551 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr028c : m.d 0 8 < m.d 0 2)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238b : m.d 3 8 < m.d 2 8)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    : False :=
  proof_shard_551 m htr012a htr013a htr023a htr025c htr026c htr027c htr028c htr035b htr045c htr046b htr123a htr125a htr126a htr127a htr128a htr129a htr135a htr137a htr235b htr237b htr238b htr245a htr246a htr345a htr345c htr346a htr356a

#print axioms shard_551
end Jsp404.NoSatElevenDBMTerminal
