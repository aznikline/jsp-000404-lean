import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_536 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237c : m.d 2 7 < m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc012zy, htr023a, htr024b, htr045a, htr124a, htr234a, htr345a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, htr134b, htr145a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd02b, hd56a, htr023a, htr234a, htr345a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd02b, hd57a, htr023a, htr234a, htr345a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd02b, hd45a, htr024a, htr246a, htr345a, htr346a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc012zy, htr024c, htr046a, htr124a, htr246a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc456xy, htr045c, htr046a, htr057a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc456xy, htr046a, htr047a, htr345a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
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
                linarith only [hlam, hc012zy, hc678yx, htr023a, htr124a, htr236a, htr246a, htr368a, htr467a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc012zy, hc678zy, htr023a, htr124a, htr237a, htr246a, htr378a, htr468a])
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
                linarith only [hlam, hc012zy, hc678xy, htr023a, htr124a, htr236a, htr246a, htr367a, htr468a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc012zy, hc678yz, htr023a, htr024b, htr047a, htr124a, htr236a, htr368a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd02b, hd67a, htr023a, htr237a, htr378a, htr678a]
              ·
                linarith only [hlam, hd02b, hd78a, htr023a, htr236a, htr367a, htr678a]
          ·
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, hc012zy, htr023a, htr024b, htr0410a, htr124a, htr234a, htr3410a])
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
              linarith only [hlam, hc456xy, htr046c, htr0610a, htr345a, htr346b, htr3610a])
            obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
            have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
              linarith only [hlam, hc457xy, htr047c, htr0710a, htr345a, htr347b, htr3710a])
            obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc012zy, hc6710yx, htr023a, htr124a, htr236a, htr246a, htr3610a, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd02b, hd67a, htr023a, htr237a, htr3710a, htr6710a]
            ·
              linarith only [hlam, hd02b, hd710a, htr023a, htr236a, htr367a, htr6710a]
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc012zy, htr023a, htr024b, htr049a, htr124a, htr234a, htr349a])
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
            linarith only [hlam, hc456xy, htr046c, htr069a, htr345a, htr346b, htr369a])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc457xy, htr047c, htr079a, htr345a, htr347b, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc012zy, hc679yx, htr023a, htr124a, htr236a, htr246a, htr369a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd02b, hd67a, htr023a, htr237a, htr379a, htr679a]
          ·
            linarith only [hlam, hd02b, hd79a, htr023a, htr236a, htr367a, htr679a]
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc012zy, htr023a, htr024b, htr048a, htr124a, htr234a, htr348a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr046b, htr048c, htr068b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr047b, htr048c, htr078b])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc456xy, htr046c, htr068a, htr345a, htr346b, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc457xy, htr047c, htr078a, htr345a, htr347b, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc012zy, hc678yx, htr023a, htr124a, htr236a, htr246a, htr368a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hd02b, hd67a, htr023a, htr237a, htr378a, htr678a]
        ·
          linarith only [hlam, hd02b, hd78a, htr023a, htr236a, htr367a, htr678a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc012zy, htr023a, htr024b, htr047a, htr124a, htr234a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr046b, htr047c, htr067b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc456xy, htr046c, htr067a, htr345a, htr346b, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc012zy, hc678xy, htr023a, htr124a, htr236a, htr246a, htr367a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd02b, hd78a, htr023a, htr234a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc467yx, htr046a, htr047c, htr078a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        linarith only [hlam, hc012zy, hc678yz, htr023a, htr025b, htr057a, htr125a, htr236a, htr368a, htr578a]
      ·
        linarith only [hlam, hc012zy, hc457yz, htr023a, htr027b, htr078a, htr127a, htr234a, htr347a, htr578a]
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc012zy, htr023a, htr024b, htr046a, htr124a, htr234a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd02b, hd67a, htr023a, htr234a, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd02b, hd68a, htr023a, htr234a, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hd02b, hd45a, htr024a, htr247a, htr345a, htr347a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc012zy, htr024c, htr047a, htr124a, htr247a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc457xy, htr045c, htr047a, htr056a, htr456a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc467xy, htr046c, htr047a, htr068a, htr468a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc456yz, htr346a, htr347a, htr467c, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc012zy, hc456yz, htr023a, htr026b, htr068a, htr126a, htr234a, htr346a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc012zy, hc678zy, htr023a, htr025b, htr056a, htr125a, htr237a, htr378a, htr568a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hd12a, hd78b, htr025b, htr056a, htr125a, htr567a, htr678a]
      ·
        linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a]
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd02b, hd78a, htr023a, htr234a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      rcases m.htr 2 5 6 (by decide) (by decide) with
        ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
      ·
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc012zy, htr025c, htr056a, htr125a, htr256a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hc012zy, hc467yz, htr023a, htr125a, htr234a, htr256a, htr347a, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc456yz, htr056a, htr057a, htr467a, htr567b])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc012zy, hc456yz, htr023a, htr026b, htr067a, htr126a, htr234a, htr346a, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc468xy, htr046c, htr048a, htr067a, htr467a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc012zy, htr024c, htr048a, htr124a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hd02b, hd45a, htr024a, htr248a, htr345a, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc012zy, hc478yz, htr023a, htr025b, htr057a, htr125a, htr234a, htr348a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a]
        ·
          linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a]
      ·
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, htr025b, htr056a, htr256a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc012zy, htr023a, htr125b, htr156a, htr235c, htr256a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc458xy, htr145c, htr148a, htr156a, htr456a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hd01b, hd45a, htr014a, htr148a, htr345a, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd02b, hd89a, htr023a, htr234a, htr348a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd02b, hd46a, htr023a, htr235c, htr256a, htr467a, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc045zy, htr056c, htr067a, htr456a, htr567a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd02b, hd46a, htr023a, htr235c, htr256a, htr468a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc012zy, hc478yz, htr023a, htr026b, htr067a, htr126a, htr234a, htr348a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc012zy, hc467yz, htr023a, htr127a, htr234a, htr278a, htr347a, htr678a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd02b, hd45a, htr023a, htr237c, htr278a, htr457a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc045zy, htr057a, htr457b, htr478a, htr578a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc457yz, htr057a, htr058a, htr478a, htr578b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45a, hd89b, htr025b, htr058a, htr256a, htr456a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc467yz, htr478a, htr568c, htr589a, htr678c, htr789a]
        ·
          linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a]

theorem shard_536 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237c : m.d 2 7 < m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_536 m htr014a htr023a htr024a htr024b htr024c htr025b htr025c htr026b htr027b htr124a htr125a htr125b htr126a htr127a htr134b htr234a htr235c htr236a htr237a htr237c htr345a

#print axioms shard_536
end Jsp404.NoSatElevenDBMTerminal
