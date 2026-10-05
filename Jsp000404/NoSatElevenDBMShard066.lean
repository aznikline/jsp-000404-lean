import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_066 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr237b : m.d 2 3 < m.d 2 7)
    (htr238b : m.d 2 3 < m.d 2 8)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr249b : m.d 4 9 < m.d 2 9)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr257b : m.d 5 7 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 2 5)
    (htr258a : m.d 5 8 + lam ≤ m.d 2 5)
    (htr258b : m.d 5 8 < m.d 2 8)
    (htr258c : m.d 2 8 < m.d 2 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < 4*lam := by
    linarith only [hd26braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
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
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc289xy, hc289yx, hc289yz, hc289zy⟩ := endpoint_caps m 2 8 9 (by decide) (by decide)
  obtain ⟨hc2910xy, hc2910yx, hc2910yz, hc2910zy⟩ := endpoint_caps m 2 9 10 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
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
  rcases m.htr 1 2 7 (by decide) (by decide) with
    ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
  ·
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd02a, hd78b, htr023a, htr123a, htr127a, htr278a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd02a, hd79b, htr023a, htr123a, htr127a, htr279a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
      linarith only [hlam, hd02a, hd710b, htr023a, htr123a, htr127a, htr2710a])
    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
    rcases m.htr 1 2 8 (by decide) (by decide) with
      ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
    ·
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hd02a, hd89b, htr023a, htr123a, htr128a, htr289a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
        linarith only [hlam, hd02a, hd810b, htr023a, htr123a, htr128a, htr2810a])
      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
      rcases m.htr 1 2 9 (by decide) (by decide) with
        ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
      ·
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, hd02a, hd910b, htr023a, htr123a, htr129a, htr2910a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        rcases m.htr 1 2 10 (by decide) (by decide) with
          ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
        ·
          rcases m.htr 4 5 6 (by decide) (by decide) with
            ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
          ·
            have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr045a, htr045b, htr045c, _, _⟩
              linarith only [hlam, hc024yz, htr045a, htr245c, htr256a, htr456a])
            obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hc245zy, htr045a, htr046a, htr256a, htr456c])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc245zy, htr256a, htr456b, htr467a, htr567a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hc245zy, htr256c, htr268a, htr456a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc245zy, htr256a, htr456b, htr468a, htr568a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hc024xy, hc278zy, htr023a, htr046a, htr123a, htr128a, htr467a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc024xy, hc289zy, htr023a, htr046a, htr123a, htr129a, htr468a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hc267zy, htr278c, htr289a, htr678a, htr789a]
            ·
              linarith only [hlam, hc267zy, htr278a, htr678b, htr689a, htr789a]
          ·
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc025yz, htr056a, htr256c, htr267a, htr567a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc256zy, htr056a, htr057a, htr267a, htr567c])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                linarith only [hlam, hc256zy, htr267a, htr456a, htr457a, htr567c])
              obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc256zy, htr267a, htr457b, htr478a, htr567b, htr678a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc256zy, htr267a, htr567b, htr578a, htr678a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hc024xy, hc278zy, htr023a, htr045a, htr123a, htr128a, htr457a, htr578a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hd24b, hd78a, htr045a, htr047a, htr245a, htr478a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc024yz, htr047a, htr247c, htr279a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd24b, hd78a, htr247a, htr479a, htr578a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc025xy, hc289zy, htr023a, htr057a, htr123a, htr129a, htr578a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc025xy, hc2910zy, htr023a, htr057a, htr1210a, htr123a, htr579a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc278zy, htr289c, htr2910a, htr789a, htr8910a]
              ·
                linarith only [hlam, hc278zy, htr289a, htr789b, htr7910a, htr8910a]
            ·
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hc024xy, hc267zy, htr023a, htr045a, htr123a, htr127a, htr456a, htr567a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                linarith only [hlam, hd24b, hd67a, htr045a, htr046a, htr245a, htr456b, htr567a])
              obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hc024yz, htr046a, htr246c, htr268a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd24b, hd67a, htr246a, htr468a, htr567a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd24b, hd78a, htr245a, htr456a, htr567a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd24b, hd89a, htr245a, htr456a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc267zy, htr278c, htr289a, htr678a, htr789a]
              ·
                linarith only [hlam, hc267zy, htr278a, htr678b, htr689a, htr789a]
        ·
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, hc256zy, htr1210a, htr126a, htr2610b, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hc257zy, htr1210a, htr127a, htr2710b, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc267zy, htr1210a, htr127a, htr2710b, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc278zy, htr1210a, htr128a, htr2810b, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          rcases m.htr 4 5 6 (by decide) (by decide) with
            ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
          ·
            have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr457a, htr457b, htr457c, _, _⟩
              linarith only [hlam, hd25b, hd710a, htr256a, htr456a, htr457a, htr5710a])
            obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc245zy, htr257c, htr278a, htr457a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd25b, hd710a, htr257a, htr578a, htr6710a, htr678a]
            ·
              linarith only [hlam, hd25b, hd810a, htr256a, htr567a, htr678a, htr7810a]
          ·
            have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr457a, htr457b, htr457c, _, _⟩
              linarith only [hlam, hd25b, hd610a, htr257a, htr456a, htr457a, htr5610a])
            obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd24b, hd710a, htr245a, htr456a, htr567a, htr6710a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd24b, hd810a, htr245a, htr457a, htr578a, htr7810a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a]
            ·
              linarith only [hlam, hd26b, hd710a, htr267a, htr5710a, htr578a, htr678a]
      ·
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc256zy, htr126a, htr129a, htr269b, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc257zy, htr127a, htr129a, htr279b, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc267zy, htr127a, htr129a, htr279b, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc278zy, htr128a, htr129a, htr289b, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 4 5 6 (by decide) (by decide) with
          ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
        ·
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hd25b, hd79a, htr256a, htr456a, htr457a, htr579a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc245zy, htr257c, htr278a, htr457a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd25b, hd79a, htr257a, htr578a, htr678a, htr679a]
          ·
            linarith only [hlam, hd25b, hd89a, htr256a, htr567a, htr678a, htr789a]
        ·
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hd25b, hd69a, htr257a, htr456a, htr457a, htr569a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hd24b, hd79a, htr245a, htr456a, htr567a, htr679a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd24b, hd89a, htr245a, htr457a, htr578a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a]
          ·
            linarith only [hlam, hd26b, hd79a, htr267a, htr578a, htr579a, htr678a]
    ·
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc245zy, htr125a, htr128a, htr258b, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc246zy, htr126a, htr128a, htr268b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc256zy, htr126a, htr128a, htr268b, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc257zy, htr127a, htr128a, htr278b, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc267zy, htr127a, htr128a, htr278b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 4 5 6 (by decide) (by decide) with
        ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
      ·
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc024yz, htr045a, htr245c, htr256a, htr456a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hd24b, hd58a, htr045a, htr046a, htr246a, htr458a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr457a, htr457b, htr457c, _, _⟩
          linarith only [hlam, hd25b, hd78a, htr256a, htr456a, htr457a, htr578a])
        obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd25b, hd68a, htr256a, htr467a, htr468a, htr567a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc245zy, htr257c, htr279a, htr457a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd25b, hd89a, htr256a, htr456a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd24b, hd58a, htr124a, htr128a, htr289a, htr589a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc024xy, hc378zy, htr023a, htr046a, htr238b, htr289a, htr389a, htr467a, htr678a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hd25b, hd78a, htr257a, htr579a, htr678a, htr679a]
        ·
          linarith only [hlam, hc014xy, hc789yz, htr013a, htr046a, htr138a, htr389a, htr467a, htr679a]
      ·
        have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr457a, htr457b, htr457c, _, _⟩
          linarith only [hlam, hd25b, hd68a, htr257a, htr456a, htr457a, htr568a])
        obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd24b, hd78a, htr245a, htr456a, htr567a, htr678a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd24b, hd68a, htr246a, htr467a, htr567a, htr568a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc024yz, htr046a, htr246c, htr267a, htr467a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hd24b, hd68a, htr045a, htr046a, htr245a, htr468a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc256zy, htr267c, htr279a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd26b, hd78a, htr267a, htr578a, htr579a, htr679a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc014xy, hc789yz, htr013a, htr045a, htr138a, htr389a, htr457a, htr579a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc024xy, hc368zy, htr023a, htr045a, htr238b, htr289a, htr389a, htr456a, htr568a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd24b, hd78a, htr124a, htr128a, htr289a, htr789a]
        ·
          linarith only [hlam, hd24b, hd89a, htr245a, htr456a, htr568a, htr678b, htr789a]
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc024yz, htr047a, htr124a, htr127a, htr247b])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc025yz, htr057a, htr125a, htr127a, htr257b])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc245zy, htr125a, htr127a, htr257b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc246zy, htr126a, htr127a, htr267b, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hc256zy, htr126a, htr127a, htr267b, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    rcases m.htr 4 5 6 (by decide) (by decide) with
      ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
    ·
      have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr045a, htr045b, htr045c, _, _⟩
        linarith only [hlam, hc024yz, htr045a, htr245c, htr256a, htr456a])
      obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hd24b, hd57a, htr045a, htr046a, htr246a, htr457a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hd24b, hd57a, htr045a, htr048a, htr248a, htr457a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc245zy, htr256c, htr268a, htr456a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd25b, hd67a, htr256a, htr467a, htr468a, htr568a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd25b, hd78a, htr256a, htr456a, htr457a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd24b, hd57a, htr124a, htr127a, htr278a, htr578a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd25b, hd79a, htr256a, htr456a, htr457a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hd24b, hd57a, htr124a, htr127a, htr279a, htr579a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      rcases m.htr 4 5 8 (by decide) (by decide) with
        ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
      ·
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc245zy, htr125a, htr128a, htr258b, htr458a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd02a, hd89b, htr023a, htr123a, htr128a, htr289a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc357zy, htr378a, htr457a, htr458a, htr578c])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd02a, hd78b, htr023a, htr237b, htr279a, htr378a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc245zy, htr258c, htr289a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc245zy, htr258a, htr458b, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc024xy, hc268zy, htr023a, htr048a, htr123a, htr128a, htr489a, htr689a]
        ·
          linarith only [hlam, hc014xy, hc789zy, htr013a, htr046a, htr137a, htr379a, htr468a, htr689a]
      ·
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd25b, hd89a, htr256a, htr456a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd01a, hd89b, htr013a, htr137a, htr378a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc025xy, hc357zy, htr023a, htr056a, htr237b, htr278a, htr378a, htr456a, htr457a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd02a, hd79b, htr023a, htr237b, htr278a, htr378a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, hc357zy, htr057a, htr059a, htr379a, htr579c])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd25b, hd910a, htr056a, htr059a, htr256a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc357zy, htr379a, htr579b, htr5910a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd02a, hd910b, htr023a, htr237b, htr278a, htr789a, htr8910a]
          ·
            linarith only [hlam, hd02a, hd89b, htr023a, htr237b, htr279a, htr7910a, htr8910a]
        ·
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, hc578yz, htr045b, htr059a, htr458a, htr589c, htr789a])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc357zy, htr378a, htr578b, htr589a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc015xy, hc578yz, htr013a, htr056a, htr137a, htr378a, htr456a, htr458a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd02a, hd78b, htr023a, htr237b, htr279a, htr378a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd25b, hd910a, htr056a, htr059a, htr256a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd01a, hd910b, htr013a, htr137a, htr379a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a]
          ·
            linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]
    ·
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hd25b, hd67a, htr258a, htr456a, htr458a, htr567a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd24b, hd78a, htr245a, htr456a, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd24b, hd67a, htr124a, htr127a, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd24b, hd79a, htr245a, htr456a, htr567a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, hd24b, hd67a, htr027c, htr079a, htr124a, htr127a, htr679a])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hd24b, hd67a, htr124a, htr127a, htr279a, htr679a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, htr047b, htr079a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr128a, htr128b, htr128c, _, _⟩
          linarith only [hlam, hc256zy, htr126a, htr128a, htr268b, htr568a])
        obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd02a, hd89b, htr023a, htr123a, htr128a, htr289a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc367zy, htr378a, htr567a, htr568a, htr678c])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd02a, hd78b, htr023a, htr237b, htr279a, htr378a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr246a, htr468a, htr567a, htr568a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc024yz, htr046a, htr246c, htr268a, htr468a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr045a, htr046a, htr245a, htr467a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc014xy, hc789zy, htr013a, htr045a, htr137a, htr379a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc256zy, htr268c, htr289a, htr568a, htr689a]
        ·
          linarith only [hlam, hc256zy, htr268a, htr568b, htr589a, htr689a]
      ·
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd24b, hd89a, htr245a, htr456a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd01a, hd89b, htr013a, htr137a, htr378a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hc024xy, hc367zy, htr023a, htr045a, htr237b, htr278a, htr378a, htr456a, htr567a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd02a, hd79b, htr023a, htr237b, htr278a, htr378a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc347zy, htr047a, htr049a, htr249b, htr279c, htr379a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd24b, hd910a, htr045a, htr049a, htr245a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc347zy, htr379a, htr479b, htr4910a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd02a, hd910b, htr023a, htr237b, htr278a, htr789a, htr8910a]
          ·
            linarith only [hlam, hd02a, hd89b, htr023a, htr237b, htr279a, htr7910a, htr8910a]
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd02a, hd78b, htr023a, htr237b, htr279a, htr378a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc678yz, htr568a, htr569a, htr689c, htr789a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd24b, hd910a, htr245a, htr456a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd01a, hd910b, htr013a, htr137a, htr379a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
          ·
            linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]

theorem shard_066 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr237b : m.d 2 3 < m.d 2 7)
    (htr238b : m.d 2 3 < m.d 2 8)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr249b : m.d 4 9 < m.d 2 9)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr257b : m.d 5 7 < m.d 2 7)
    (htr257c : m.d 2 7 < m.d 2 5)
    (htr258a : m.d 5 8 + lam ≤ m.d 2 5)
    (htr258b : m.d 5 8 < m.d 2 8)
    (htr258c : m.d 2 8 < m.d 2 5)
    : False :=
  proof_shard_066 m htr013a htr023a htr027c htr123a htr124a htr125a htr126a htr137a htr138a htr237b htr238b htr245a htr245c htr246a htr246c htr247a htr247b htr247c htr248a htr249b htr256a htr256c htr257a htr257b htr257c htr258a htr258b htr258c

#print axioms shard_066
end Jsp404.NoSatElevenDBMTerminal
