import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_359 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < 4*lam := by
    linarith only [hd26braw, hp]
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
  have hd68a := (m.hrange 6 8 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, htr024c, htr034b, htr245a, htr345a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd13b, hd56a, htr013a, htr014a, htr134b, htr345a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hd13b, hd45a, htr013a, htr015a, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd13b, hd57a, htr013a, htr014a, htr134b, htr345a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hd13b, hd45a, htr013a, htr015a, htr157a, htr457a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd13b, hd58a, htr013a, htr014a, htr134b, htr345a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hd13b, hd45a, htr013a, htr015a, htr158a, htr458a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hd13b, hd45a, htr013a, htr014c, htr046a, htr345a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hc245zy, htr256a, htr345a, htr346a, htr456c])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc456xy, htr046a, htr047a, htr345a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc245zy, htr257a, htr345a, htr347a, htr457c])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      rcases m.htr 2 4 6 (by decide) (by decide) with
        ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
      ·
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc456xy, htr246a, htr247a, htr345a, htr347a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
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
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc123xy, hc678yx, htr013a, htr016a, htr124a, htr168a, htr246a, htr467a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc456xy, htr136b, htr168a, htr345a, htr346b, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc123xy, hc678zy, htr013a, htr017a, htr124a, htr178a, htr246a, htr468a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc457xy, htr137b, htr178a, htr345a, htr347b, htr478a])
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
                  linarith only [hlam, hc123xy, hc678xy, htr013a, htr016a, htr124a, htr136b, htr246a, htr367a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc456xy, htr136b, htr168a, htr345a, htr346b, htr468a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr124a, htr168a, htr247a, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc457xy, htr137b, htr178a, htr345a, htr347b, htr478a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a]
                ·
                  linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr136b, htr367a, htr678a]
            ·
              have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                linarith only [hlam, htr034b, htr0410a, htr3410a])
              obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                linarith only [hlam, htr0410c, htr046b, htr0610b])
              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, htr0410c, htr047b, htr0710b])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                linarith only [hlam, hc136yx, htr013a, htr016c, htr0610a, htr1610a])
              obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hc137yx, htr013a, htr017c, htr0710a, htr1710a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc123xy, hc6710yx, htr013a, htr016a, htr124a, htr1610a, htr246a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc456xy, htr136b, htr167a, htr345a, htr346b, htr467a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              rcases m.htr 6 7 10 (by decide) (by decide) with
                ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              ·
                linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr1710a, htr6710a]
              ·
                linarith only [hlam, hd13b, hd710a, htr013a, htr016a, htr167a, htr6710a]
          ·
            have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr049a, htr049b, htr049c, _, _⟩
              linarith only [hlam, htr034b, htr049a, htr349a])
            obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr046b, htr049c, htr069b])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, htr047b, htr049c, htr079b])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr169a, htr169b, htr169c, _, _⟩
              linarith only [hlam, hc136yx, htr013a, htr016c, htr069a, htr169a])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc137yx, htr013a, htr017c, htr079a, htr179a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc123xy, hc679yx, htr013a, htr016a, htr124a, htr169a, htr246a, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc456xy, htr136b, htr167a, htr345a, htr346b, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr179a, htr679a]
            ·
              linarith only [hlam, hd13b, hd79a, htr013a, htr016a, htr167a, htr679a]
        ·
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr034b, htr048a, htr348a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr046b, htr048c, htr068b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr047b, htr048c, htr078b])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc136yx, htr013a, htr016c, htr068a, htr168a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc123xy, hc678yx, htr013a, htr016a, htr124a, htr168a, htr246a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc456xy, htr136b, htr167a, htr345a, htr346b, htr467a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a]
          ·
            linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a]
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
                  linarith only [hlam, hd26b, hd45a, htr267a, htr345a, htr346a, htr467a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc123xy, hc678yx, htr013a, htr016a, htr125a, htr168a, htr256a, htr567a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hd45a, hd67b, htr136b, htr168a, htr267a, htr268a, htr345a, htr346b])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd45a, hd67b, htr246b, htr268a, htr345a, htr346a, htr567a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc123xy, hc678zy, htr013a, htr017a, htr125a, htr178a, htr256a, htr568a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc457xy, htr137b, htr178a, htr345a, htr347b, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd45a, hd78b, htr345a, htr346a, htr467a, htr678a]
                ·
                  linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a]
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc456xy, htr136b, htr167a, htr345a, htr346b, htr467a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc123xy, hc678xy, htr013a, htr016a, htr125a, htr167a, htr256a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr468a, htr568a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc456xy, htr136b, htr168a, htr345a, htr346b, htr468a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr125a, htr168a, htr257a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd45a, hd57b, htr345a, htr347a, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc457xy, htr137b, htr178a, htr345a, htr347b, htr478a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a]
                ·
                  linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a]
            ·
              have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                linarith only [hlam, htr034b, htr0410a, htr3410a])
              obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                linarith only [hlam, htr0410c, htr046b, htr0610b])
              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, htr0410c, htr047b, htr0710b])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hc137yx, htr013a, htr017c, htr0710a, htr1710a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                linarith only [hlam, htr046c, htr0610a, htr4610a])
              obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc6710yx, htr034b, htr046a, htr3410a, htr4610b, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc456xy, htr136b, htr167a, htr345a, htr346b, htr467a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              rcases m.htr 6 7 10 (by decide) (by decide) with
                ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              ·
                linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr1710a, htr6710a]
              ·
                linarith only [hlam, hd13b, hd710a, htr013a, htr016a, htr167a, htr6710a]
          ·
            have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr049a, htr049b, htr049c, _, _⟩
              linarith only [hlam, htr034b, htr049a, htr349a])
            obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr046b, htr049c, htr069b])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, htr047b, htr049c, htr079b])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc137yx, htr013a, htr017c, htr079a, htr179a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr469a, htr469b, htr469c, _, _⟩
              linarith only [hlam, htr046c, htr069a, htr469a])
            obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc679yx, htr034b, htr046a, htr349a, htr467a, htr469b])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc456xy, htr136b, htr167a, htr345a, htr346b, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr179a, htr679a]
            ·
              linarith only [hlam, hd13b, hd79a, htr013a, htr016a, htr167a, htr679a]
        ·
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr034b, htr048a, htr348a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr046b, htr048c, htr068b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr047b, htr048c, htr078b])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
            linarith only [hlam, htr046c, htr068a, htr468a])
          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc678yx, htr034b, htr046a, htr348a, htr467a, htr468b])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc456xy, htr136b, htr167a, htr345a, htr346b, htr467a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a]
          ·
            linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr034b, htr047a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr046b, htr047c, htr067b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, htr046c, htr067a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc678xy, htr034b, htr046a, htr347a, htr467b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc456xy, htr136b, htr168a, htr345a, htr346b, htr468a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc679xy, htr034b, htr046a, htr347a, htr467b, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc456xy, htr136b, htr169a, htr345a, htr346b, htr469a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
        linarith only [hlam, hc6710xy, htr034b, htr046a, htr347a, htr4610a, htr467b])
      obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
      have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
        linarith only [hlam, hc456xy, htr136b, htr1610a, htr345a, htr346b, htr4610a])
      obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr013a, htr014a, htr134b, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc467yx, htr046a, htr047c, htr078a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, htr467b, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd13b, hd89a, htr013a, htr016a, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd13b, hd68a, htr013a, htr018a, htr189a, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hd13b, hd810a, htr013a, htr016a, htr168a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hd13b, hd68a, htr013a, htr018a, htr1810a, htr6810a])
      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc123xy, hc268zy, htr012b, htr013a, htr016a, htr027b, htr078a, htr168a, htr289a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc138yx, hc689yz, htr013a, htr016a, htr169a, htr1810a, htr2810a, htr289a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc135yx, hc689yz, htr013a, htr016a, htr157a, htr169a, htr578a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc245zy, htr257a, htr457b, htr478a, htr578a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc135yx, hc457yz, htr013a, htr014a, htr134b, htr158a, htr257a, htr258a, htr347a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 5 8 10 (by decide) (by decide) with
          ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
        ·
          linarith only [hlam, hc123xy, hc6810yz, htr013a, htr016a, htr125a, htr1610a, htr258a, htr5810a]
        ·
          linarith only [hlam, hc123xy, hc568zy, htr013a, htr016a, htr128a, htr168a, htr2810a, htr5810a]
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr128a, htr168a, htr289a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc138yx, hc6810yz, htr013a, htr016a, htr1610a, htr189a, htr2810a, htr289a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr125a, htr168a, htr257a, htr578a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc135yx, hc568zy, htr013a, htr016a, htr157a, htr168a, htr257a, htr258a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 5 8 10 (by decide) (by decide) with
          ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
        ·
          linarith only [hlam, hc135yx, hc268zy, htr013a, htr016a, htr158a, htr168a, htr2810a, htr5810a]
        ·
          linarith only [hlam, hd56b, hd68a, htr256a, htr258a, htr5810a, htr6810a]
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd13b, hd67a, htr013a, htr014a, htr134b, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hd13b, hd46a, htr013a, htr016a, htr167a, htr467a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd13b, hd68a, htr013a, htr014a, htr134b, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hd13b, hd46a, htr013a, htr016a, htr168a, htr468a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd13b, hd45a, htr013a, htr014c, htr047a, htr345a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc245zy, htr257a, htr345a, htr347a, htr457c])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc456yz, htr346a, htr347a, htr467c, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 2 5 6 (by decide) (by decide) with
        ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc135yx, hc456yz, htr013a, htr014a, htr134b, htr158a, htr256a, htr258a, htr346a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12a, hd78b, htr125a, htr256a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc457xy, htr137b, htr178a, htr345a, htr347b, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc123xy, hc678zy, htr013a, htr017a, htr125a, htr178a, htr256a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc456yz, htr034b, htr048a, htr346a, htr468c, htr568a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc457xy, htr047a, htr048a, htr134b, htr148a, htr345a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc789xy, htr047a, htr048a, htr478b, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc457xy, htr137b, htr179a, htr345a, htr347b, htr479a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd13b, hd89a, htr013a, htr014a, htr148a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc123xy, hc789yz, htr013a, htr017a, htr125a, htr179a, htr258a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc136yx, hc578zy, htr013a, htr017a, htr168a, htr178a, htr589a, htr689a]
        ·
          linarith only [hlam, hc456yz, htr468b, htr489a, htr568a, htr689a]
      ·
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc457xy, htr245c, htr247a, htr256a, htr456a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc245zy, htr256a, htr456b, htr468a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd45a, hd78b, htr256a, htr257a, htr456a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd45a, hd57b, htr345a, htr347a, htr478a, htr578a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc457xy, htr137b, htr178a, htr345a, htr347b, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc135yx, hc578zy, htr013a, htr017a, htr156a, htr178a, htr256a, htr258a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc245zy, htr034b, htr048a, htr258a, htr345a, htr458c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc789xy, htr047a, htr048a, htr478b, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc457xy, htr137b, htr179a, htr345a, htr347b, htr479a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd24b, hd89a, htr047a, htr048a, htr247a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc245zy, htr258a, htr458b, htr489a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc135yx, hc789yz, htr013a, htr017a, htr156a, htr179a, htr568a, htr689a]
        ·
          linarith only [hlam, hc135yx, hc678zy, htr013a, htr017a, htr158a, htr178a, htr589a, htr689a]
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr013a, htr014a, htr134b, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd13b, hd79a, htr013a, htr014a, htr134b, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc123xy, hc467yz, htr013a, htr014a, htr125a, htr134b, htr256a, htr347a, htr567a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc135yx, hc457yz, htr013a, htr014a, htr134b, htr156a, htr256a, htr257a, htr347a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc245zy, htr257a, htr457b, htr478a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc245zy, htr257a, htr457b, htr479a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc135yx, hc467yz, htr013a, htr014a, htr134b, htr157a, htr347a, htr578a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc135yx, hc478yz, htr013a, htr014a, htr148a, htr156a, htr567a, htr678a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc245zy, htr134b, htr148a, htr258a, htr345a, htr458c])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45a, hd89b, htr256a, htr258a, htr456a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd45a, hd58b, htr134b, htr148a, htr345a, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc458xy, htr134b, htr148b, htr189a, htr345a, htr489a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc135yx, hc789zy, htr013a, htr018a, htr156a, htr189a, htr567a, htr679a]
        ·
          linarith only [hlam, hc135yx, hc467yz, htr013a, htr014a, htr134b, htr157a, htr347a, htr579a, htr679a]
      ·
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc245zy, htr256a, htr456b, htr467a, htr567a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc135yx, hc456yz, htr013a, htr014a, htr134b, htr157a, htr256a, htr257a, htr346a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc136yx, hc457yz, htr013a, htr014a, htr134b, htr167a, htr347a, htr578a, htr678a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc123xy, hc478yz, htr013a, htr014a, htr125a, htr148a, htr257a, htr578a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc456yz, htr467b, htr479a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc136yx, hc457yz, htr013a, htr014a, htr134b, htr167a, htr347a, htr579a, htr679a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc123xy, hc789zy, htr013a, htr018a, htr125a, htr189a, htr257a, htr579a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc458xy, htr134b, htr148b, htr189a, htr345a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd89b, htr125a, htr257a, htr578a, htr789a]
        ·
          linarith only [hlam, hd45a, hd78b, htr134b, htr148a, htr345a, htr489a, htr789a]

theorem shard_359 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_359 m htr012b htr013a htr014a htr014c htr015a htr016a htr016c htr017a htr017c htr018a htr024c htr027b htr034b htr124a htr125a htr128a htr134b htr136b htr137b htr345a

#print axioms shard_359
end Jsp404.NoSatElevenDBMTerminal
