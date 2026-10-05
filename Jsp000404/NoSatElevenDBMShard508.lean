import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_508 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246b : m.d 4 6 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 2 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
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
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
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
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd12a, hd56b, htr023a, htr025a, htr123a, htr256a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hd12a, hd57b, htr023a, htr025a, htr123a, htr257a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hd12a, hd58b, htr023a, htr025a, htr123a, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, hd12a, hd59b, htr023a, htr025a, htr123a, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, hd12a, hd510b, htr023a, htr025a, htr123a, htr2510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  rcases m.htr 0 2 6 (by decide) (by decide) with
    ⟨htr026a, htr026b, htr026c, _, _⟩ | ⟨htr026a, htr026b, htr026c, _, _⟩
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr023a, htr026a, htr123a, htr267a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd12a, hd68b, htr023a, htr026a, htr123a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hd12a, hd69b, htr023a, htr026a, htr123a, htr269a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
      linarith only [hlam, hd12a, hd610b, htr023a, htr026a, htr123a, htr2610a])
    obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
    rcases m.htr 0 2 7 (by decide) (by decide) with
      ⟨htr027a, htr027b, htr027c, _, _⟩ | ⟨htr027a, htr027b, htr027c, _, _⟩
    ·
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr023a, htr027a, htr123a, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hd12a, hd79b, htr023a, htr027a, htr123a, htr279a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hd12a, hd710b, htr023a, htr027a, htr123a, htr2710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      rcases m.htr 0 2 8 (by decide) (by decide) with
        ⟨htr028a, htr028b, htr028c, _, _⟩ | ⟨htr028a, htr028b, htr028c, _, _⟩
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr023a, htr028a, htr123a, htr289a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 0 2 9 (by decide) (by decide) with
          ⟨htr029a, htr029b, htr029c, _, _⟩ | ⟨htr029a, htr029b, htr029c, _, _⟩
        ·
          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
            linarith only [hlam, hd12a, hd910b, htr023a, htr029a, htr123a, htr2910a])
          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
          rcases m.htr 0 2 10 (by decide) (by decide) with
            ⟨htr0210a, htr0210b, htr0210c, _, _⟩ | ⟨htr0210a, htr0210b, htr0210c, _, _⟩
          ·
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr145a, htr145b, htr145c, _, _⟩
                linarith only [hlam, hc124yz, htr145a, htr245c, htr256a, htr456a])
              obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hc245zy, htr145a, htr146a, htr256a, htr456c])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
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
                linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd01b, hd89a, htr014a, htr146a, htr468a, htr689a])
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
                have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                  linarith only [hlam, hc125yz, htr156a, htr256c, htr267a, htr567a])
                obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hc256zy, htr156a, htr157a, htr267a, htr567c])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
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
                have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr145a, htr145b, htr145c, _, _⟩
                  linarith only [hlam, hd01b, hd78a, htr014a, htr145a, htr457a, htr578a])
                obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
                have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr147a, htr147b, htr147c, _, _⟩
                  linarith only [hlam, hd24b, hd78a, htr145a, htr147a, htr245a, htr478a])
                obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc124yz, htr147a, htr247c, htr279a, htr479a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd24b, hd78a, htr247a, htr479a, htr578a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd01b, hd89a, htr015a, htr157a, htr578a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hd01b, hd910a, htr015a, htr157a, htr579a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hc278zy, htr289c, htr2910a, htr789a, htr8910a]
                ·
                  linarith only [hlam, hc278zy, htr289a, htr789b, htr7910a, htr8910a]
              ·
                have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr145a, htr145b, htr145c, _, _⟩
                  linarith only [hlam, hd01b, hd67a, htr014a, htr145a, htr456a, htr567a])
                obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
                have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                  linarith only [hlam, hd24b, hd67a, htr145a, htr146a, htr245a, htr456b, htr567a])
                obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc124yz, htr146a, htr246c, htr268a, htr468a])
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
            have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
              linarith only [hlam, hc245zy, htr0210a, htr025a, htr2510b, htr4510a])
            obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, hc246zy, htr0210a, htr026a, htr2610b, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              linarith only [hlam, hc256zy, htr0210a, htr026a, htr2610b, htr5610a])
            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc267zy, htr0210a, htr027a, htr2710b, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr145a, htr145b, htr145c, _, _⟩
                linarith only [hlam, hc124yz, htr145a, htr245c, htr256a, htr456a])
              obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hd24b, hd510a, htr145a, htr146a, htr246a, htr4510a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd01b, hd710a, htr014a, htr146a, htr467a, htr6710a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              rcases m.htr 5 6 7 (by decide) (by decide) with
                ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
              ·
                linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a]
              ·
                linarith only [hlam, hd25b, hd610a, htr256a, htr4610a, htr467a, htr567a]
            ·
              have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr145a, htr145b, htr145c, _, _⟩
                linarith only [hlam, hd01b, hd610a, htr014a, htr145a, htr456a, htr5610a])
              obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
              have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr146a, htr146b, htr146c, _, _⟩
                linarith only [hlam, hd24b, hd610a, htr145a, htr146a, htr245a, htr4610a])
              obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc124yz, htr146a, htr246c, htr267a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              rcases m.htr 5 6 7 (by decide) (by decide) with
                ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
              ·
                linarith only [hlam, hd24b, hd610a, htr246a, htr467a, htr5610a, htr567a]
              ·
                linarith only [hlam, hd24b, hd710a, htr245a, htr456a, htr567a, htr6710a]
        ·
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, hc245zy, htr025a, htr029a, htr259b, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hc246zy, htr026a, htr029a, htr269b, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc256zy, htr026a, htr029a, htr269b, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc267zy, htr027a, htr029a, htr279b, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          rcases m.htr 4 5 6 (by decide) (by decide) with
            ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
          ·
            have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr145a, htr145b, htr145c, _, _⟩
              linarith only [hlam, hc124yz, htr145a, htr245c, htr256a, htr456a])
            obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hd24b, hd59a, htr145a, htr146a, htr246a, htr459a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd01b, hd79a, htr014a, htr146a, htr467a, htr679a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a]
            ·
              linarith only [hlam, hd25b, hd69a, htr256a, htr467a, htr469a, htr567a]
          ·
            have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr145a, htr145b, htr145c, _, _⟩
              linarith only [hlam, hd01b, hd69a, htr014a, htr145a, htr456a, htr569a])
            obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
            have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr146a, htr146b, htr146c, _, _⟩
              linarith only [hlam, hd24b, hd69a, htr145a, htr146a, htr245a, htr469a])
            obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc124yz, htr146a, htr246c, htr267a, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              linarith only [hlam, hd24b, hd69a, htr246a, htr467a, htr567a, htr569a]
            ·
              linarith only [hlam, hd24b, hd79a, htr245a, htr456a, htr567a, htr679a]
      ·
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, hc245zy, htr025a, htr028a, htr258b, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc246zy, htr026a, htr028a, htr268b, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc256zy, htr026a, htr028a, htr268b, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc267zy, htr027a, htr028a, htr278b, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 4 5 6 (by decide) (by decide) with
          ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
        ·
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hc124yz, htr145a, htr245c, htr256a, htr456a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hd24b, hd58a, htr145a, htr146a, htr246a, htr458a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd01b, hd78a, htr014a, htr146a, htr467a, htr678a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a]
          ·
            linarith only [hlam, hd25b, hd68a, htr256a, htr467a, htr468a, htr567a]
        ·
          have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr145a, htr145b, htr145c, _, _⟩
            linarith only [hlam, hd01b, hd68a, htr014a, htr145a, htr456a, htr568a])
          obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
          have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr146a, htr146b, htr146c, _, _⟩
            linarith only [hlam, hd24b, hd68a, htr145a, htr146a, htr245a, htr468a])
          obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc124yz, htr146a, htr246c, htr267a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            linarith only [hlam, hd24b, hd68a, htr246a, htr467a, htr567a, htr568a]
          ·
            linarith only [hlam, hd24b, hd78a, htr245a, htr456a, htr567a, htr678a]
    ·
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc124yz, htr024a, htr027a, htr147a, htr247b])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, hc245zy, htr025a, htr027a, htr257b, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc246zy, htr026a, htr027a, htr267b, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc256zy, htr026a, htr027a, htr267b, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 4 5 6 (by decide) (by decide) with
        ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
      ·
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hc124yz, htr145a, htr245c, htr256a, htr456a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hd24b, hd57a, htr145a, htr146a, htr246a, htr457a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc245zy, htr256c, htr268a, htr456a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd25b, hd67a, htr256a, htr467a, htr468a, htr568a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc245zy, htr256c, htr269a, htr456a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hd25b, hd67a, htr256a, htr467a, htr469a, htr569a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd25b, hd78a, htr256a, htr456a, htr457a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd24b, hd57a, htr024a, htr027a, htr278a, htr578a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd25b, hd79a, htr256a, htr456a, htr457a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hd24b, hd57a, htr024a, htr027a, htr279a, htr579a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, htr567b, htr578a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, htr567b, htr579a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr014a, htr146a, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd01b, hd910a, htr014a, htr146a, htr469a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd12a, hd79b, htr127a, htr278a, htr378a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd910b, htr127a, htr278a, htr789a, htr8910a]
          ·
            linarith only [hlam, hd12a, hd89b, htr127a, htr279a, htr7910a, htr8910a]
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd12a, hd78b, htr127a, htr279a, htr378a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd12a, hd910b, htr123a, htr237a, htr379a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
          ·
            linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
      ·
        have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr145a, htr145b, htr145c, _, _⟩
          linarith only [hlam, hd01b, hd67a, htr014a, htr145a, htr456a, htr567a])
        obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr145a, htr146a, htr245a, htr467a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc124yz, htr146a, htr246c, htr268a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc124yz, htr146a, htr246c, htr269a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd24b, hd78a, htr145a, htr147a, htr245a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd24b, hd47a, htr024a, htr027a, htr278a, htr478a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd24b, hd79a, htr145a, htr147a, htr245a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hd24b, hd47a, htr024a, htr027a, htr279a, htr479a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr246a, htr468a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr246a, htr469a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, htr467b, htr478a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, htr467b, htr479a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd24b, hd89a, htr245a, htr456a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd24b, hd910a, htr245a, htr456a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd12a, hd89b, htr123a, htr237a, htr378a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd12a, hd79b, htr127a, htr278a, htr378a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd910b, htr127a, htr278a, htr789a, htr8910a]
          ·
            linarith only [hlam, hd12a, hd89b, htr127a, htr279a, htr7910a, htr8910a]
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd12a, hd78b, htr127a, htr279a, htr378a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd12a, hd910b, htr123a, htr237a, htr379a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
          ·
            linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
  ·
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hc124yz, htr024a, htr026a, htr146a, htr246b])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hc245zy, htr025a, htr026a, htr256b, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    rcases m.htr 1 4 5 (by decide) (by decide) with
      ⟨htr145a, htr145b, htr145c, _, _⟩ | ⟨htr145a, htr145b, htr145c, _, _⟩
    ·
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, hc124yz, htr145a, htr245c, htr257a, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc124yz, htr145a, htr245c, htr258a, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr459a, htr459b, htr459c, _, _⟩
        linarith only [hlam, hc124yz, htr145a, htr245c, htr259a, htr459a])
      obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd24b, hd67a, htr145a, htr146a, htr245a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd24b, hd46a, htr024a, htr026a, htr267a, htr467a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd24b, hd68a, htr145a, htr146a, htr245a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd24b, hd46a, htr024a, htr026a, htr268a, htr468a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hd24b, hd69a, htr145a, htr146a, htr245a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hd24b, hd46a, htr024a, htr026a, htr269a, htr469a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      rcases m.htr 3 6 7 (by decide) (by decide) with
        ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
      ·
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd12a, hd67b, htr126a, htr268a, htr367a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hd12a, hd67b, htr126a, htr269a, htr367a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12a, hd78b, htr123a, htr236a, htr367a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd12a, hd79b, htr123a, htr236a, htr367a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr123a, htr236a, htr368a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd12a, hd910b, htr123a, htr236a, htr369a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            linarith only [hlam, hd24b, hd910a, htr245a, htr458a, htr589a, htr8910a])
          obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd24b, hd89a, htr245a, htr459a, htr5910a, htr8910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr147a, htr147b, htr147c, _, _⟩
              linarith only [hlam, hd24b, hd79a, htr145a, htr147a, htr245a, htr479a])
            obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hd46a, hd67b, htr146a, htr147a, htr478a, htr678a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            rcases m.htr 5 7 9 (by decide) (by decide) with
              ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
            ·
              linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
            ·
              linarith only [hlam, hd24b, hd79a, htr247a, htr478a, htr578a, htr579a]
          ·
            rcases m.htr 5 7 9 (by decide) (by decide) with
              ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
            ·
              linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a]
            ·
              linarith only [hlam, hd24b, hd89a, htr245a, htr457a, htr579a, htr7910a, htr8910a]
        ·
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hd24b, hd78a, htr145a, htr147a, htr245a, htr457b, htr578a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd46a, hd67b, htr146a, htr147a, htr479a, htr679a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd24b, hd78a, htr247a, htr479a, htr578a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd24b, hd89a, htr245a, htr457a, htr578a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd24b, hd910a, htr245a, htr457a, htr579a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
          ·
            linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
      ·
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc346zy, htr146a, htr147a, htr367a, htr467c])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd12a, hd68b, htr126a, htr267a, htr367a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc346zy, htr146a, htr148a, htr368a, htr468c])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd24b, hd78a, htr145a, htr147a, htr245a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd24b, hd89a, htr145a, htr148a, htr245a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc346zy, htr367a, htr467b, htr478a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc346zy, htr368a, htr468b, htr489a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd89b, htr126a, htr267a, htr678a, htr789a]
        ·
          linarith only [hlam, hd12a, hd78b, htr126a, htr268a, htr689a, htr789a]
    ·
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hd24b, hd56a, htr145a, htr147a, htr247a, htr456a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hd01b, hd67a, htr014a, htr145a, htr456a, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd24b, hd56a, htr024a, htr026a, htr267a, htr567a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hd01b, hd68a, htr014a, htr145a, htr456a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hd24b, hd56a, htr024a, htr026a, htr268a, htr568a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hd01b, hd69a, htr014a, htr145a, htr456a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hd24b, hd56a, htr024a, htr026a, htr269a, htr569a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      rcases m.htr 4 5 7 (by decide) (by decide) with
        ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
      ·
        have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr027a, htr027b, htr027c, _, _⟩
          linarith only [hlam, hc245zy, htr025a, htr027a, htr257b, htr457a])
        obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd12a, hd78b, htr023a, htr027a, htr123a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hd12a, hd79b, htr023a, htr027a, htr123a, htr279a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc356zy, htr367a, htr456a, htr457a, htr567c])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hd12a, hd67b, htr126a, htr268a, htr367a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hd12a, hd67b, htr126a, htr269a, htr367a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc245zy, htr257c, htr278a, htr457a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc245zy, htr257a, htr457b, htr478a, htr578a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc245zy, htr257c, htr279a, htr457a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc245zy, htr257a, htr457b, htr479a, htr579a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr123a, htr236a, htr368a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd12a, hd910b, htr123a, htr236a, htr369a, htr6910a])
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
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd01b, hd78a, htr014a, htr145a, htr457a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hd12a, hd78b, htr123a, htr236a, htr367a, htr678a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, hd12a, hd68b, htr126a, htr267a, htr367a, htr368a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr458a, htr458b, htr458c, _, _⟩
            linarith only [hlam, hc356zy, htr368a, htr456a, htr458a, htr568c])
          obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd01b, hd89a, htr014a, htr145a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc356zy, htr368a, htr568b, htr589a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd89b, htr126a, htr267a, htr678a, htr789a]
          ·
            linarith only [hlam, hd12a, hd78b, htr126a, htr268a, htr689a, htr789a]
        ·
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, hd12a, hd67b, htr126a, htr268a, htr367a, htr368a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr458a, htr458b, htr458c, _, _⟩
            linarith only [hlam, hc567yz, htr457a, htr458a, htr578c, htr678a])
          obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd01b, hd89a, htr014a, htr145a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hd12a, hd89b, htr123a, htr236a, htr368a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
          ·
            linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]

theorem shard_508 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246b : m.d 4 6 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 2 4)
    : False :=
  proof_shard_508 m htr014a htr015a htr023a htr024a htr025a htr123a htr126a htr127a htr236a htr237a htr245a htr245c htr246a htr246b htr246c htr247a htr247b htr247c

#print axioms shard_508
end Jsp404.NoSatElevenDBMTerminal
