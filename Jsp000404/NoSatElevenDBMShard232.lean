import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_232 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr239a : m.d 3 9 + lam ≤ m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd06a, hd06braw⟩ := m.hrange 0 6 (by decide)
  have hd06b : m.d 0 6 < 4*lam := by
    linarith only [hd06braw, hp]
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd16a, hd16braw⟩ := m.hrange 1 6 (by decide)
  have hd16b : m.d 1 6 < 4*lam := by
    linarith only [hd16braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
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
  have hd69a := (m.hrange 6 9 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  have hd810a := (m.hrange 8 10 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc025xy, hc025yx, hc025yz, hc025zy⟩ := endpoint_caps m 0 2 5 (by decide) (by decide)
  obtain ⟨hc027xy, hc027yx, hc027yz, hc027zy⟩ := endpoint_caps m 0 2 7 (by decide) (by decide)
  obtain ⟨hc028xy, hc028yx, hc028yz, hc028zy⟩ := endpoint_caps m 0 2 8 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc148xy, hc148yx, hc148yz, hc148zy⟩ := endpoint_caps m 1 4 8 (by decide) (by decide)
  obtain ⟨hc168xy, hc168yx, hc168yz, hc168zy⟩ := endpoint_caps m 1 6 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
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
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr024b, htr045a, htr234b, htr345a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc012xy, htr014a, htr023a, htr145a, htr234a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr123a, htr234a, htr345a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd12b, hd57a, htr123a, htr234a, htr345a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd12b, hd58a, htr123a, htr234a, htr345a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr123a, htr235a, htr358a, htr458a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc145zy, htr156a, htr345a, htr346a, htr456c])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr124a, htr246a, htr345a, htr346a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc145zy, htr157a, htr345a, htr347a, htr457c])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc456xy, htr246a, htr247a, htr345a, htr347a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        rcases m.htr 1 4 6 (by decide) (by decide) with
          ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
        ·
          have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr046a, htr046b, htr046c, _, _⟩
            linarith only [hlam, htr014c, htr046a, htr146a])
          obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
          have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr047a, htr047b, htr047c, _, _⟩
            linarith only [hlam, hc456xy, htr014c, htr047a, htr146a, htr345a, htr347a])
          obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
          have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr147a, htr147b, htr147c, _, _⟩
            linarith only [hlam, hc456xy, htr146a, htr147a, htr345a, htr347a])
          obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
          rcases m.htr 3 4 9 (by decide) (by decide) with
            ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
          ·
            rcases m.htr 3 4 10 (by decide) (by decide) with
              ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
            ·
              rcases m.htr 3 6 7 (by decide) (by decide) with
                ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
              ·
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc012xy, hc678yx, htr014a, htr023a, htr146a, htr236a, htr368a, htr467a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc012xy, hc678zy, htr014a, htr023a, htr146a, htr237a, htr378a, htr468a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd45a, hd78b, htr345a, htr346a, htr467a, htr678a]
                ·
                  linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a]
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc012xy, hc678xy, htr014a, htr023a, htr146a, htr236a, htr367a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc012xy, hc678yz, htr014a, htr023a, htr147a, htr236a, htr368a, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a]
                ·
                  linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
            ·
              have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                linarith only [hlam, htr024b, htr0410a, htr234b, htr3410a])
              obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                linarith only [hlam, htr0410c, htr046b, htr0610b])
              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, htr0410c, htr047b, htr0710b])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
                linarith only [hlam, hc456xy, htr016c, htr0610a, htr146c, htr345a, htr346b, htr3610a])
              obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
              have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                linarith only [hlam, hc457xy, htr047c, htr0710a, htr345a, htr347b, htr3710a])
              obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc012xy, hc6710yx, htr014a, htr023a, htr146a, htr236a, htr3610a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              rcases m.htr 6 7 10 (by decide) (by decide) with
                ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              ·
                linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr3710a, htr6710a]
              ·
                linarith only [hlam, hd12b, hd710a, htr123a, htr236a, htr367a, htr6710a]
          ·
            have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr049a, htr049b, htr049c, _, _⟩
              linarith only [hlam, htr024b, htr049a, htr234b, htr349a])
            obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr046b, htr049c, htr069b])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, htr047b, htr049c, htr079b])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr369a, htr369b, htr369c, _, _⟩
              linarith only [hlam, hc456xy, htr016c, htr069a, htr146c, htr345a, htr346b, htr369a])
            obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc457xy, htr047c, htr079a, htr345a, htr347b, htr379a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc012xy, hc679yx, htr014a, htr023a, htr146a, htr236a, htr369a, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr379a, htr679a]
            ·
              linarith only [hlam, hd12b, hd79a, htr123a, htr236a, htr367a, htr679a]
        ·
          rcases m.htr 3 4 9 (by decide) (by decide) with
            ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
          ·
            rcases m.htr 0 4 6 (by decide) (by decide) with
              ⟨htr046a, htr046b, htr046c, _, _⟩ | ⟨htr046a, htr046b, htr046c, _, _⟩
            ·
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc456xy, htr046a, htr047a, htr345a, htr347a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              rcases m.htr 3 4 10 (by decide) (by decide) with
                ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
              ·
                rcases m.htr 4 6 7 (by decide) (by decide) with
                  ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                ·
                  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                    linarith only [hlam, hd16b, hd45a, htr167a, htr345a, htr346a, htr467a])
                  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hc012xy, hc678yx, htr015a, htr023a, htr156a, htr236a, htr368a, htr567a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, hd45a, hd67b, htr167a, htr168a, htr345a, htr346b, htr368a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hd45a, hd67b, htr146b, htr168a, htr345a, htr346a, htr567a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc012xy, hc678zy, htr015a, htr023a, htr156a, htr237a, htr378a, htr568a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd45a, hd78b, htr345a, htr346a, htr467a, htr678a]
                  ·
                    linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a]
                ·
                  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                    linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
                  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hc012xy, hc678xy, htr015a, htr023a, htr156a, htr236a, htr367a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr468a, htr568a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc012xy, hc678yz, htr015a, htr023a, htr157a, htr236a, htr368a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hd45a, hd57b, htr345a, htr347a, htr478a, htr578a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a]
                  ·
                    linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
              ·
                have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                  linarith only [hlam, htr024b, htr0410a, htr234b, htr3410a])
                obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, htr0410c, htr046b, htr0610b])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                  linarith only [hlam, htr0410c, htr047b, htr0710b])
                obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                  linarith only [hlam, hc457xy, htr047c, htr0710a, htr345a, htr347b, htr3710a])
                obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                  linarith only [hlam, htr046c, htr0610a, htr4610a])
                obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc6710yx, htr234b, htr246a, htr3410a, htr4610b, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                rcases m.htr 6 7 10 (by decide) (by decide) with
                  ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                ·
                  linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr3710a, htr6710a]
                ·
                  linarith only [hlam, hd12b, hd710a, htr123a, htr236a, htr367a, htr6710a]
            ·
              rcases m.htr 3 4 10 (by decide) (by decide) with
                ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
              ·
                rcases m.htr 4 6 7 (by decide) (by decide) with
                  ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                ·
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, hd06b, hd45a, htr067a, htr345a, htr346a, htr467a])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hc012xy, hc678yx, htr015a, htr023a, htr156a, htr236a, htr368a, htr567a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hd45a, hd67b, htr067a, htr068a, htr345a, htr346b, htr368a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hd45a, hd67b, htr046b, htr068a, htr345a, htr346a, htr567a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc012xy, hc678zy, htr015a, htr023a, htr156a, htr237a, htr378a, htr568a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd45a, hd78b, htr345a, htr346a, htr467a, htr678a]
                  ·
                    linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a]
                ·
                  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                    linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
                  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hc012xy, hc678xy, htr015a, htr023a, htr156a, htr236a, htr367a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr468a, htr568a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc012xy, hc678yz, htr015a, htr023a, htr157a, htr236a, htr368a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hd45a, hd57b, htr345a, htr347a, htr478a, htr578a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a]
                  ·
                    linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
              ·
                have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
                  linarith only [hlam, htr234b, htr2410a, htr3410a])
                obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
                have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                  linarith only [hlam, htr2410c, htr246b, htr2610b])
                obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
                have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                  linarith only [hlam, htr2410c, htr247b, htr2710b])
                obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                  linarith only [hlam, hd12b, hd45a, htr127a, htr2710a, htr345a, htr347b, htr3710a])
                obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                  linarith only [hlam, htr246c, htr2610a, htr4610a])
                obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc6710yx, htr234b, htr246a, htr3410a, htr4610b, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                rcases m.htr 6 7 10 (by decide) (by decide) with
                  ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                ·
                  linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr3710a, htr6710a]
                ·
                  linarith only [hlam, hd12b, hd710a, htr123a, htr236a, htr367a, htr6710a]
          ·
            have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr249a, htr249b, htr249c, _, _⟩
              linarith only [hlam, htr234b, htr249a, htr349a])
            obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
            have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr269a, htr269b, htr269c, _, _⟩
              linarith only [hlam, htr246b, htr249c, htr269b])
            obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, htr247b, htr249c, htr279b])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hd12b, hd45a, htr127a, htr279a, htr345a, htr347b, htr379a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr469a, htr469b, htr469c, _, _⟩
              linarith only [hlam, htr246c, htr269a, htr469a])
            obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc679yx, htr234b, htr246a, htr349a, htr467a, htr469b])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr379a, htr679a]
            ·
              linarith only [hlam, hd12b, hd79a, htr123a, htr236a, htr367a, htr679a]
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr234b, htr248a, htr348a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr246b, htr248c, htr268b])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr247b, htr248c, htr278b])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd12b, hd45a, htr127a, htr278a, htr345a, htr347b, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr246c, htr268a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc678yx, htr234b, htr246a, htr348a, htr467a, htr468b])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a]
        ·
          linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr024b, htr047a, htr234b, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc012xy, htr014a, htr023a, htr147a, htr234a, htr347a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr234b, htr247a, htr347a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, htr246b, htr247c, htr267b])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, htr246c, htr267a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc678xy, htr234b, htr246a, htr347a, htr467b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc679xy, htr234b, htr246a, htr347a, htr467b, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hc456xy, htr345a, htr346b, htr369a, htr469a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
        linarith only [hlam, hc6710xy, htr234b, htr246a, htr347a, htr4610a, htr467b])
      obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
      have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
        linarith only [hlam, hc456xy, htr345a, htr346b, htr3610a, htr4610a])
      obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr123a, htr234a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd12b, hd79a, htr123a, htr234a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, htr467b, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12b, hd89a, htr123a, htr236a, htr368a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr123a, htr238a, htr389a, htr689a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hd12b, hd810a, htr123a, htr236a, htr368a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr123a, htr238a, htr3810a, htr6810a])
      obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd12b, hd910a, htr123a, htr236a, htr369a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
        linarith only [hlam, hd12b, hd69a, htr123a, htr239a, htr3910a, htr6910a])
      obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc147zy, htr178a, htr347a, htr348a, htr478c])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc458xy, htr345a, htr348b, htr389a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc012xy, hc689yz, htr017a, htr023a, htr178a, htr236a, htr369a, htr789a]
        ·
          linarith only [hlam, hd45a, hd78b, htr345a, htr348a, htr489a, htr789a]
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr024b, htr048a, htr234b, htr348a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, htr348b, htr389a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 1 4 6 (by decide) (by decide) with
          ⟨htr146a, htr146b, htr146c, _, _⟩ | ⟨htr146a, htr146b, htr146c, _, _⟩
        ·
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc456xy, htr145c, htr146a, htr157a, htr457a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc467yx, htr146a, htr147c, htr178a, htr478a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          rcases m.htr 5 7 8 (by decide) (by decide) with
            ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
          ·
            linarith only [hlam, hc012xy, hc678yz, htr015a, htr023a, htr157a, htr236a, htr368a, htr578a]
          ·
            linarith only [hlam, hc012xy, hc457yz, htr017a, htr023a, htr178a, htr234a, htr347a, htr578a]
        ·
          rcases m.htr 3 4 9 (by decide) (by decide) with
            ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
          ·
            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
              linarith only [hlam, hc148zy, htr189a, htr348a, htr349a, htr489c])
            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hc459xy, htr345a, htr349b, htr3910a, htr4910a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hc012xy, hc6910yz, htr018a, htr023a, htr189a, htr236a, htr3610a, htr8910a]
            ·
              linarith only [hlam, hd45a, hd89b, htr345a, htr349a, htr4910a, htr8910a]
          ·
            rcases m.htr 0 4 6 (by decide) (by decide) with
              ⟨htr046a, htr046b, htr046c, _, _⟩ | ⟨htr046a, htr046b, htr046c, _, _⟩
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc456xy, htr045c, htr046a, htr057a, htr457a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                linarith only [hlam, hc456xy, htr045c, htr046a, htr058a, htr458a])
              obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc467yx, htr046a, htr047c, htr078a, htr478a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, hc456xy, htr046a, htr048c, htr089a, htr345b, htr358b, htr389a])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                linarith only [hlam, hc456xy, htr046a, htr048c, htr0810a, htr345b, htr358b, htr3810a])
              obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc027yx, hc168zy, htr023a, htr078a, htr189a, htr236a, htr368a, htr789a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc028yx, hc689yz, htr023a, htr0810a, htr1810a, htr189a, htr236a, htr369a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc025yx, hc689yz, htr023a, htr057a, htr236a, htr369a, htr578a, htr789a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hc145zy, htr157a, htr457b, htr478a, htr578a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, hc025yx, hc457yz, htr023a, htr058a, htr157a, htr158a, htr234a, htr347a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                rcases m.htr 5 8 10 (by decide) (by decide) with
                  ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                ·
                  linarith only [hlam, hc012xy, hc6810yz, htr015a, htr023a, htr158a, htr236a, htr3610a, htr5810a]
                ·
                  linarith only [hlam, hc012xy, hc568zy, htr018a, htr023a, htr1810a, htr236a, htr368a, htr5810a]
              ·
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc012xy, hc678yz, htr018a, htr023a, htr189a, htr236a, htr368a, htr789a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc028yx, hc6810yz, htr023a, htr089a, htr1810a, htr189a, htr236a, htr3610a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hc012xy, hc678yz, htr015a, htr023a, htr157a, htr236a, htr368a, htr578a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, hc025yx, hc568zy, htr023a, htr057a, htr157a, htr158a, htr236a, htr368a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                rcases m.htr 5 8 10 (by decide) (by decide) with
                  ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                ·
                  linarith only [hlam, hc025yx, hc168zy, htr023a, htr058a, htr1810a, htr236a, htr368a, htr5810a]
                ·
                  linarith only [hlam, hd56b, hd68a, htr156a, htr158a, htr5810a, htr6810a]
            ·
              rcases m.htr 1 5 7 (by decide) (by decide) with
                ⟨htr157a, htr157b, htr157c, _, _⟩ | ⟨htr157a, htr157b, htr157c, _, _⟩
              ·
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc012xy, hc678yz, htr015a, htr023a, htr157a, htr236a, htr368a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, hc457yz, htr157a, htr158a, htr478a, htr578b])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc012xy, hc689yz, htr015a, htr023a, htr158a, htr236a, htr369a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hc457yz, htr478a, htr578c, htr589a, htr789a]
                ·
                  linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a]
              ·
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc145zy, htr157a, htr457b, htr478a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc145zy, htr157c, htr178a, htr457a, htr578a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc145zy, htr157a, htr457b, htr479a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc145zy, htr157c, htr179a, htr457a, htr579a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc012xy, hc689yz, htr017a, htr023a, htr178a, htr236a, htr369a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc012xy, hc6910yz, htr017a, htr023a, htr179a, htr236a, htr3610a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
                ·
                  linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr123a, htr234a, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd12b, hd68a, htr123a, htr234a, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd12b, hd69a, htr123a, htr234a, htr346a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc145zy, htr157a, htr345a, htr347a, htr457c])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc146zy, htr167a, htr346a, htr347a, htr467c])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hd12b, hd45a, htr124a, htr247a, htr345a, htr347a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc456yz, htr346a, htr347a, htr467c, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc145zy, htr158a, htr345a, htr348a, htr458c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc456yz, htr346a, htr348a, htr468c, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        rcases m.htr 1 5 6 (by decide) (by decide) with
          ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
        ·
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc012xy, hc678zy, htr015a, htr023a, htr156a, htr237a, htr378a, htr568a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a]
          ·
            linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a]
        ·
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd45a, hd78b, htr156a, htr157a, htr456a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd45a, hd57b, htr345a, htr347a, htr478a, htr578a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd45a, hd89b, htr156a, htr158a, htr456a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd45a, hd58b, htr345a, htr348a, htr489a, htr589a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc458xy, htr345a, htr348b, htr389a, htr489a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr389a, htr789a]
          ·
            linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, htr234b, htr248a, htr348a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr247b, htr248c, htr278b])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, htr247c, htr278a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc789xy, htr234b, htr247a, htr348a, htr478b, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc457xy, htr345a, htr347b, htr379a, htr479a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hc7810xy, htr234b, htr247a, htr348a, htr4710a, htr478b])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
          linarith only [hlam, hc457xy, htr345a, htr347b, htr3710a, htr4710a])
        obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr123a, htr234a, htr348a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, htr478b, htr489a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd12b, hd910a, htr123a, htr237a, htr379a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 1 5 6 (by decide) (by decide) with
          ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
        ·
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hd45a, hd67b, htr156a, htr158a, htr458a, htr567a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr568a, htr568b, htr568c, _, _⟩
            linarith only [hlam, hc012xy, hc468yz, htr015a, htr023a, htr156a, htr234a, htr348a, htr568a])
          obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc012xy, hc789yz, htr015a, htr023a, htr158a, htr237a, htr379a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 6 8 9 (by decide) (by decide) with
            ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
          ·
            linarith only [hlam, hc456yz, htr468a, htr568c, htr589a, htr689a]
          ·
            linarith only [hlam, hc456yz, htr468b, htr489a, htr568a, htr689a]
        ·
          have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr568a, htr568b, htr568c, _, _⟩
            linarith only [hlam, hc145zy, htr156a, htr456b, htr468a, htr568a])
          obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hd45a, hd67b, htr167a, htr168a, htr456a, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc145zy, htr156a, htr456b, htr469a, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hd45a, hd67b, htr167a, htr169a, htr456a, htr569a])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc012xy, hc789yz, htr016a, htr023a, htr168a, htr237a, htr379a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc012xy, hc7910yz, htr016a, htr023a, htr169a, htr237a, htr3710a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc468yz, htr489a, htr689c, htr6910a, htr8910a]
          ·
            linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd12b, hd78a, htr123a, htr234a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd12b, hd79a, htr123a, htr234a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc145zy, htr158a, htr345a, htr348a, htr458c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc146zy, htr168a, htr346a, htr348a, htr468c])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc456yz, htr346a, htr348a, htr468c, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc457yz, htr347a, htr348a, htr478c, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc467yz, htr347a, htr348a, htr478c, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc012xy, hc467yz, htr015a, htr023a, htr156a, htr234a, htr347a, htr567a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hd45a, hd78b, htr156a, htr157a, htr456a, htr578a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hd45a, hd68b, htr167a, htr168a, htr456a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc145zy, htr157a, htr457b, htr479a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd45a, hd89b, htr156a, htr158a, htr456a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd45a, hd58b, htr345a, htr348a, htr489a, htr589a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc458xy, htr345a, htr348b, htr389a, htr489a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hc012xy, hc789zy, htr016a, htr023a, htr167a, htr238a, htr389a, htr679a]
          ·
            linarith only [hlam, hd45a, hd78b, htr457a, htr579a, htr678a, htr679a]
        ·
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr567a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hd45a, hd68b, htr156a, htr157a, htr457a, htr568a])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc456yz, htr467b, htr479a, htr567a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd46a, hd78b, htr467a, htr578a, htr579a, htr679a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc012xy, hc789zy, htr015a, htr023a, htr157a, htr238a, htr389a, htr579a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc458xy, htr345a, htr348b, htr389a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd46a, hd89b, htr467a, htr567a, htr568a, htr678c, htr789a]
          ·
            linarith only [hlam, hd45a, hd78b, htr345a, htr348a, htr489a, htr789a]
      ·
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr123a, htr234a, htr348a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 1 5 6 (by decide) (by decide) with
          ⟨htr156a, htr156b, htr156c, _, _⟩ | ⟨htr156a, htr156b, htr156c, _, _⟩
        ·
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc012xy, hc467yz, htr015a, htr023a, htr156a, htr234a, htr347a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr157a, htr157b, htr157c, _, _⟩
            linarith only [hlam, hc456yz, htr156a, htr157a, htr467a, htr567b])
          obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc012xy, hc478yz, htr015a, htr023a, htr157a, htr234a, htr348a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a]
          ·
            linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a]
        ·
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc145zy, htr156a, htr456b, htr467a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc145zy, htr156c, htr167a, htr456a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr568a, htr568b, htr568c, _, _⟩
            linarith only [hlam, hc145zy, htr156a, htr456b, htr468a, htr568a])
          obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc145zy, htr156c, htr168a, htr456a, htr568a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hc012xy, hc478yz, htr016a, htr023a, htr167a, htr234a, htr348a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc012xy, hc467yz, htr017a, htr023a, htr178a, htr234a, htr347a, htr678a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc467yz, htr478a, htr568c, htr589a, htr678c, htr789a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hd45a, hd89b, htr156a, htr158a, htr456a, htr589a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr349a, htr349b, htr349c, _, _⟩
            linarith only [hlam, hc012xy, hc489yz, htr016a, htr023a, htr168a, htr234a, htr349a, htr689a])
          obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hc147zy, htr179a, htr347a, htr349a, htr479c])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd45a, hd79b, htr178a, htr179a, htr457a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 1 5 7 (by decide) (by decide) with
            ⟨htr157a, htr157b, htr157c, _, _⟩ | ⟨htr157a, htr157b, htr157c, _, _⟩
          ·
            linarith only [hlam, hc457yz, htr157a, htr158a, htr478a, htr578b]
          ·
            linarith only [hlam, hc145zy, htr157a, htr457b, htr478a, htr578a]

theorem shard_232 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr239a : m.d 3 9 + lam ≤ m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    : False :=
  proof_shard_232 m htr014a htr014c htr015a htr016a htr016c htr017a htr018a htr023a htr024b htr123a htr124a htr127a htr234a htr234b htr235a htr236a htr237a htr238a htr239a htr345a htr345b

#print axioms shard_232
end Jsp404.NoSatElevenDBMTerminal
