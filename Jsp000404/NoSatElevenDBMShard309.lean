import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_309 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
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
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
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
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, htr234c, htr245a, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr012a, htr014a, htr124b, htr245a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr012a, htr015a, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd12b, hd57a, htr012a, htr014a, htr124b, htr245a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr012a, htr015a, htr157a, htr457a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hc125yx, htr012a, htr015c, htr057a, htr157a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, htr035b, htr037c, htr057b])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd12b, hd58a, htr012a, htr014a, htr124b, htr245a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr012a, htr015a, htr158a, htr458a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, hc125yx, htr012a, htr015c, htr058a, htr158a])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, htr035b, htr038c, htr058b])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  rcases m.htr 2 4 6 (by decide) (by decide) with
    ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hd12b, hd45a, htr012a, htr014c, htr046a, htr245a, htr246a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc345zy, htr245a, htr246a, htr356a, htr456c])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc456xy, htr345c, htr346a, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      rcases m.htr 3 4 7 (by decide) (by decide) with
        ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr034c, htr047a, htr347a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc123yx, htr012a, htr014a, htr134a, htr147a, htr347a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        rcases m.htr 3 4 8 (by decide) (by decide) with
          ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
        ·
          rcases m.htr 3 4 9 (by decide) (by decide) with
            ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
          ·
            rcases m.htr 3 4 10 (by decide) (by decide) with
              ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
            ·
              rcases m.htr 2 6 7 (by decide) (by decide) with
                ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
              ·
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc456xy, htr245a, htr246b, htr267a, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc123yx, hc678yx, htr012a, htr016a, htr134a, htr168a, htr346a, htr467a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc456xy, htr126b, htr168a, htr245a, htr246b, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc123yx, hc678zy, htr012a, htr017a, htr134a, htr178a, htr346a, htr468a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc457xy, htr124b, htr147b, htr178a, htr245a, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd45a, hd78b, htr245a, htr246a, htr467a, htr678a]
                ·
                  linarith only [hlam, hd23a, hd67b, htr234a, htr347a, htr478a, htr678a]
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc123yx, hc678xy, htr012a, htr016a, htr126b, htr134a, htr267a, htr346a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc456xy, htr126b, htr168a, htr245a, htr246b, htr468a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc123yx, hc678yz, htr012a, htr016a, htr134a, htr168a, htr347a, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc457xy, htr124b, htr147b, htr178a, htr245a, htr478a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a]
                ·
                  linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr126b, htr267a, htr678a]
            ·
              have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                linarith only [hlam, hc456xy, htr024b, htr0410a, htr245a, htr3410a, htr346a])
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
                linarith only [hlam, hc126yx, htr012a, htr016c, htr0610a, htr1610a])
              obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hc127yx, htr012a, htr017c, htr0710a, htr1710a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc123yx, hc6710yx, htr012a, htr016a, htr134a, htr1610a, htr346a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc456xy, htr126b, htr167a, htr245a, htr246b, htr467a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              rcases m.htr 6 7 10 (by decide) (by decide) with
                ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              ·
                linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr1710a, htr6710a]
              ·
                linarith only [hlam, hd12b, hd710a, htr012a, htr016a, htr167a, htr6710a]
          ·
            have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr049a, htr049b, htr049c, _, _⟩
              linarith only [hlam, hc456xy, htr024b, htr049a, htr245a, htr346a, htr349a])
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
              linarith only [hlam, hc126yx, htr012a, htr016c, htr069a, htr169a])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc127yx, htr012a, htr017c, htr079a, htr179a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc123yx, hc679yx, htr012a, htr016a, htr134a, htr169a, htr346a, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc456xy, htr126b, htr167a, htr245a, htr246b, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr179a, htr679a]
            ·
              linarith only [hlam, hd12b, hd79a, htr012a, htr016a, htr167a, htr679a]
        ·
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc456xy, htr024b, htr048a, htr245a, htr346a, htr348a])
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
            linarith only [hlam, hc126yx, htr012a, htr016c, htr068a, htr168a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc127yx, htr012a, htr017c, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc123yx, hc678yx, htr012a, htr016a, htr134a, htr168a, htr346a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc456xy, htr126b, htr167a, htr245a, htr246b, htr467a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a]
          ·
            linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr167a, htr678a]
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc456xy, htr024b, htr047a, htr245a, htr346a, htr347a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr046b, htr047c, htr067b])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc456xy, htr124b, htr147a, htr245a, htr346a, htr347a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc126yx, htr012a, htr016c, htr067a, htr167a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc123yx, hc678xy, htr012a, htr016a, htr134a, htr167a, htr346a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc456xy, htr126b, htr168a, htr245a, htr246b, htr468a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr012a, htr014a, htr147a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc467yx, htr346a, htr347c, htr378a, htr478a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          linarith only [hlam, hc123yx, hc678yz, htr012a, htr016a, htr135a, htr168a, htr357a, htr578a]
        ·
          linarith only [hlam, hc123yx, hc457yz, htr012a, htr013b, htr014a, htr037a, htr147a, htr378a, htr578a]
    ·
      rcases m.htr 2 4 7 (by decide) (by decide) with
        ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc456xy, htr046a, htr047a, htr245a, htr247a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, hc345zy, htr245a, htr247a, htr357a, htr457c])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        rcases m.htr 2 4 8 (by decide) (by decide) with
          ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
        ·
          rcases m.htr 2 4 9 (by decide) (by decide) with
            ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
          ·
            rcases m.htr 2 4 10 (by decide) (by decide) with
              ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
            ·
              rcases m.htr 4 6 7 (by decide) (by decide) with
                ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
              ·
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hd36b, hd45a, htr245a, htr246a, htr367a, htr467a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd45a, hd56b, htr245a, htr246a, htr467a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc123yx, hc678yx, htr012a, htr016a, htr135a, htr168a, htr356a, htr567a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd45a, hd67b, htr126b, htr168a, htr245a, htr246b, htr367a, htr368a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd45a, hd67b, htr245a, htr246a, htr346b, htr368a, htr567a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc123yx, hc678zy, htr012a, htr017a, htr135a, htr178a, htr356a, htr568a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc457xy, htr127b, htr178a, htr245a, htr247b, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd45a, hd78b, htr245a, htr246a, htr467a, htr678a]
                ·
                  linarith only [hlam, hd45a, hd67b, htr245a, htr247a, htr478a, htr678a]
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc456xy, htr126b, htr167a, htr245a, htr246b, htr467a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc123yx, hc678xy, htr012a, htr016a, htr135a, htr167a, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hd45a, hd56b, htr245a, htr246a, htr468a, htr568a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc456xy, htr126b, htr168a, htr245a, htr246b, htr468a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc123yx, hc678yz, htr012a, htr016a, htr135a, htr168a, htr357a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd45a, hd57b, htr245a, htr247a, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc457xy, htr127b, htr178a, htr245a, htr247b, htr478a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a]
                ·
                  linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr167a, htr678a]
            ·
              have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                linarith only [hlam, htr024b, htr0410a, htr2410a])
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
                linarith only [hlam, hc127yx, htr012a, htr017c, htr0710a, htr1710a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                linarith only [hlam, htr046c, htr0610a, htr4610a])
              obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc6710yx, htr024b, htr046a, htr2410a, htr4610b, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc456xy, htr126b, htr167a, htr245a, htr246b, htr467a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              rcases m.htr 6 7 10 (by decide) (by decide) with
                ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              ·
                linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr1710a, htr6710a]
              ·
                linarith only [hlam, hd12b, hd710a, htr012a, htr016a, htr167a, htr6710a]
          ·
            have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr049a, htr049b, htr049c, _, _⟩
              linarith only [hlam, htr024b, htr049a, htr249a])
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
              linarith only [hlam, hc127yx, htr012a, htr017c, htr079a, htr179a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr469a, htr469b, htr469c, _, _⟩
              linarith only [hlam, htr046c, htr069a, htr469a])
            obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc679yx, htr024b, htr046a, htr249a, htr467a, htr469b])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc456xy, htr126b, htr167a, htr245a, htr246b, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr179a, htr679a]
            ·
              linarith only [hlam, hd12b, hd79a, htr012a, htr016a, htr167a, htr679a]
        ·
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr024b, htr048a, htr248a])
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
            linarith only [hlam, hc127yx, htr012a, htr017c, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
            linarith only [hlam, htr046c, htr068a, htr468a])
          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc678yx, htr024b, htr046a, htr248a, htr467a, htr468b])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc456xy, htr126b, htr167a, htr245a, htr246b, htr467a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a]
          ·
            linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr167a, htr678a]
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr024b, htr047a, htr247a])
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
          linarith only [hlam, hc678xy, htr024b, htr046a, htr247a, htr467b, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc456xy, htr126b, htr168a, htr245a, htr246b, htr468a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc679xy, htr024b, htr046a, htr247a, htr467b, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, hc456xy, htr126b, htr169a, htr245a, htr246b, htr469a])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
          linarith only [hlam, hc6710xy, htr024b, htr046a, htr247a, htr4610a, htr467b])
        obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
        have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
          linarith only [hlam, hc456xy, htr126b, htr1610a, htr245a, htr246b, htr4610a])
        obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr012a, htr014a, htr124b, htr247a, htr478a])
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
          linarith only [hlam, hd12b, hd89a, htr012a, htr016a, htr168a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hd12b, hd68a, htr012a, htr018a, htr189a, htr689a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hd12b, hd810a, htr012a, htr016a, htr168a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hd12b, hd68a, htr012a, htr018a, htr1810a, htr6810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc127yx, hc368zy, htr012a, htr016a, htr017b, htr078a, htr168a, htr389a, htr789a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, hc128yx, hc689yz, htr012a, htr016a, htr169a, htr1810a, htr3810a, htr389a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc125yx, hc689yz, htr012a, htr016a, htr157a, htr169a, htr578a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hc345zy, htr357a, htr457b, htr478a, htr578a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc125yx, hc457yz, htr012a, htr014a, htr124b, htr158a, htr247a, htr357a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          rcases m.htr 5 8 10 (by decide) (by decide) with
            ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          ·
            linarith only [hlam, hc123yx, hc6810yz, htr012a, htr016a, htr135a, htr1610a, htr358a, htr5810a]
          ·
            linarith only [hlam, hc123yx, hc568zy, htr012a, htr013b, htr016a, htr038a, htr168a, htr3810a, htr5810a]
        ·
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc123yx, hc678yz, htr012a, htr013b, htr016a, htr038a, htr168a, htr389a, htr789a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, hc128yx, hc6810yz, htr012a, htr016a, htr1610a, htr189a, htr3810a, htr389a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hc123yx, hc678yz, htr012a, htr016a, htr135a, htr168a, htr357a, htr578a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc125yx, hc568zy, htr012a, htr016a, htr157a, htr168a, htr357a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          rcases m.htr 5 8 10 (by decide) (by decide) with
            ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          ·
            linarith only [hlam, hc125yx, hc368zy, htr012a, htr016a, htr158a, htr168a, htr3810a, htr5810a]
          ·
            linarith only [hlam, hd56b, hd68a, htr356a, htr358a, htr5810a, htr6810a]
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd12b, hd67a, htr012a, htr014a, htr124b, htr246a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd12b, hd68a, htr012a, htr014a, htr124b, htr246a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hd12b, hd46a, htr012a, htr016a, htr168a, htr468a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    rcases m.htr 3 5 6 (by decide) (by decide) with
      ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
    ·
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc125yx, hc456yz, htr012a, htr014a, htr124b, htr157a, htr246a, htr356a, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc125yx, hc456yz, htr012a, htr014a, htr124b, htr158a, htr246a, htr356a, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc123yx, hc467yz, htr012a, htr014a, htr135a, htr147a, htr356a, htr567a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc124yx, htr012a, htr014c, htr047a, htr147a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr235a, htr356a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr124b, htr147a, htr245a, htr478a, htr678a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc457xy, htr124b, htr147b, htr178a, htr245a, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc123yx, hc678zy, htr012a, htr017a, htr135a, htr178a, htr356a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc456yz, htr024b, htr048a, htr246a, htr468c, htr568a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc457xy, htr047a, htr048a, htr124b, htr148a, htr245a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc789xy, htr047a, htr048a, htr478b, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc457xy, htr124b, htr147b, htr179a, htr245a, htr479a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr012a, htr014a, htr148a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc123yx, hc789yz, htr012a, htr017a, htr135a, htr179a, htr358a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc126yx, hc578zy, htr012a, htr017a, htr168a, htr178a, htr589a, htr689a]
        ·
          linarith only [hlam, hc456yz, htr468b, htr489a, htr568a, htr689a]
      ·
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc456yz, htr124b, htr147a, htr246a, htr467c, htr567a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr012a, htr014a, htr147a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd12b, hd79a, htr012a, htr014a, htr147a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc123yx, hc478yz, htr012a, htr014a, htr135a, htr148a, htr357a, htr578a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc456yz, htr467b, htr479a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc456yz, htr467a, htr567c, htr579a, htr679a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc123yx, hc789zy, htr012a, htr018a, htr135a, htr189a, htr357a, htr579a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc458xy, htr124b, htr148b, htr189a, htr245a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd89b, htr235a, htr357a, htr578a, htr789a]
        ·
          linarith only [hlam, hd45a, hd78b, htr124b, htr148a, htr245a, htr489a, htr789a]
    ·
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, hc457xy, htr345c, htr347a, htr356a, htr456a])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc345zy, htr356a, htr456b, htr467a, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc345zy, htr356a, htr456b, htr468a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      rcases m.htr 3 5 7 (by decide) (by decide) with
        ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
      ·
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc125yx, hc457yz, htr012a, htr014a, htr147a, htr156a, htr356a, htr357a])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, hc124yx, htr012a, htr014c, htr047a, htr147a])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd45a, hd78b, htr356a, htr357a, htr456a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd45a, hd57b, htr124b, htr147a, htr245a, htr478a, htr578a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc457xy, htr124b, htr147b, htr178a, htr245a, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc125yx, hc578zy, htr012a, htr017a, htr156a, htr178a, htr356a, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc345zy, htr024b, htr048a, htr245a, htr358a, htr458c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc789xy, htr047a, htr048a, htr478b, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc457xy, htr124b, htr147b, htr179a, htr245a, htr479a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd34b, hd89a, htr047a, htr048a, htr347a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc345zy, htr358a, htr458b, htr489a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc125yx, hc789yz, htr012a, htr017a, htr156a, htr179a, htr568a, htr689a]
        ·
          linarith only [hlam, hc125yx, hc678zy, htr012a, htr017a, htr158a, htr178a, htr589a, htr689a]
      ·
        have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr147a, htr147b, htr147c, _, _⟩
          linarith only [hlam, hc345zy, htr124b, htr147a, htr245a, htr357a, htr457c])
        obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr012a, htr014a, htr147a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd12b, hd79a, htr012a, htr014a, htr147a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc345zy, htr357a, htr457b, htr478a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc345zy, htr357a, htr457b, htr479a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc125yx, hc467yz, htr012a, htr014a, htr147a, htr157a, htr578a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc125yx, hc478yz, htr012a, htr014a, htr148a, htr156a, htr567a, htr678a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc345zy, htr124b, htr148a, htr245a, htr358a, htr458c])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45a, hd89b, htr356a, htr358a, htr456a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd45a, hd58b, htr124b, htr148a, htr245a, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc458xy, htr124b, htr148b, htr189a, htr245a, htr489a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc125yx, hc789zy, htr012a, htr018a, htr156a, htr189a, htr567a, htr679a]
        ·
          linarith only [hlam, hc125yx, hc467yz, htr012a, htr014a, htr147a, htr157a, htr579a, htr679a]

theorem shard_309 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    : False :=
  proof_shard_309 m htr012a htr013b htr014a htr014c htr015a htr015c htr016a htr016c htr017a htr017b htr017c htr018a htr024b htr034c htr035b htr124b htr126b htr127b htr134a htr135a htr234a htr234c htr235a htr245a

#print axioms shard_309
end Jsp404.NoSatElevenDBMTerminal
