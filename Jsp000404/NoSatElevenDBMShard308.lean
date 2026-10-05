import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_308 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr038a : m.d 0 3 + lam ≤ m.d 3 8)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd79a := (m.hrange 7 9 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc234yz, htr025b, htr056a, htr245b, htr345a, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc234yz, htr125b, htr156a, htr245b, htr345a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc234yz, htr245b, htr256a, htr345a, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd12b, hd67a, htr012a, htr015a, htr156a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr012a, htr016a, htr167a, htr567a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc126yx, htr012a, htr016c, htr067a, htr167a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd12b, hd68a, htr012a, htr015a, htr156a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hd12b, hd56a, htr012a, htr016a, htr168a, htr568a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  rcases m.htr 2 4 6 (by decide) (by decide) with
    ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc234yz, htr045a, htr046a, htr246a, htr345a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, htr046b, htr047c, htr067b])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc234yz, htr126b, htr167a, htr246b, htr345a, htr456c, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc234yz, htr126b, htr168a, htr246b, htr345a, htr456c, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      rcases m.htr 4 5 7 (by decide) (by decide) with
        ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
      ·
        linarith only [hlam, hc567xy, htr345a, htr347a, htr456a, htr457c]
      ·
        linarith only [hlam, hc457zy, htr345a, htr347a, htr457a]
    ·
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          linarith only [hlam, hc568xy, htr345a, htr348a, htr456a, htr458c]
        ·
          linarith only [hlam, hc458zy, htr345a, htr348a, htr458a]
      ·
        rcases m.htr 2 5 7 (by decide) (by decide) with
          ⟨htr257a, htr257b, htr257c, _, _⟩ | ⟨htr257a, htr257b, htr257c, _, _⟩
        ·
          have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr057a, htr057b, htr057c, _, _⟩
            linarith only [hlam, hc234yz, htr045c, htr057a, htr245b, htr257a, htr345a])
          obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hc234yz, htr245b, htr257a, htr345a, htr457a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr357a, htr357b, htr357c, _, _⟩
            linarith only [hlam, hc234yz, htr245a, htr345c, htr357a, htr457a])
          obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
          rcases m.htr 4 5 8 (by decide) (by decide) with
            ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
          ·
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, htr045c, htr058a, htr458a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, hc124yx, htr012a, htr015a, htr145a, htr158a, htr458a])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            rcases m.htr 4 5 9 (by decide) (by decide) with
              ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
            ·
              rcases m.htr 4 5 10 (by decide) (by decide) with
                ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
              ·
                rcases m.htr 2 7 8 (by decide) (by decide) with
                  ⟨htr278a, htr278b, htr278c, _, _⟩ | ⟨htr278a, htr278b, htr278c, _, _⟩
                ·
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc567xy, htr256a, htr257b, htr278a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc124yx, hc789yx, htr012a, htr017a, htr145a, htr179a, htr457a, htr578a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc567xy, htr127b, htr179a, htr256a, htr257b, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc124yx, hc789zy, htr012a, htr018a, htr145a, htr189a, htr457a, htr579a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc568xy, htr156a, htr158b, htr189a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd56a, hd89b, htr256a, htr257a, htr578a, htr789a]
                  ·
                    linarith only [hlam, hd24a, hd78b, htr245a, htr458a, htr589a, htr789a]
                ·
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc124yx, hc789xy, htr012a, htr017a, htr127b, htr145a, htr278a, htr457a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc567xy, htr127b, htr179a, htr256a, htr257b, htr579a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc124yx, hc789yz, htr012a, htr017a, htr145a, htr179a, htr458a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc568xy, htr156a, htr158b, htr189a, htr589a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd12b, hd78a, htr012a, htr018a, htr189a, htr789a]
                  ·
                    linarith only [hlam, hd12b, hd89a, htr012a, htr017a, htr127b, htr278a, htr789a]
              ·
                have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                  linarith only [hlam, hc567xy, htr0510a, htr056a, htr4510a, htr457a])
                obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                  linarith only [hlam, htr0510c, htr057b, htr0710b])
                obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0510c, htr058b, htr0810b])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                  linarith only [hlam, hc127yx, htr012a, htr017c, htr0710a, htr1710a])
                obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc128yx, htr012a, htr018c, htr0810a, htr1810a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc124yx, hc7810yx, htr012a, htr017a, htr145a, htr1710a, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc567xy, htr127b, htr178a, htr256a, htr257b, htr578a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 7 8 10 (by decide) (by decide) with
                  ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                ·
                  linarith only [hlam, hd12b, hd78a, htr012a, htr018a, htr1810a, htr7810a]
                ·
                  linarith only [hlam, hd12b, hd810a, htr012a, htr017a, htr178a, htr7810a]
            ·
              have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                linarith only [hlam, hc567xy, htr056a, htr059a, htr457a, htr459a])
              obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, htr057b, htr059c, htr079b])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, htr058b, htr059c, htr089b])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc127yx, htr012a, htr017c, htr079a, htr179a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc128yx, htr012a, htr018c, htr089a, htr189a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc124yx, hc789yx, htr012a, htr017a, htr145a, htr179a, htr457a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc567xy, htr127b, htr178a, htr256a, htr257b, htr578a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd12b, hd78a, htr012a, htr018a, htr189a, htr789a]
              ·
                linarith only [hlam, hd12b, hd89a, htr012a, htr017a, htr178a, htr789a]
          ·
            have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr058a, htr058b, htr058c, _, _⟩
              linarith only [hlam, hc567xy, htr056a, htr058a, htr457a, htr458a])
            obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr057b, htr058c, htr078b])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr158a, htr158b, htr158c, _, _⟩
              linarith only [hlam, hc567xy, htr156a, htr158a, htr457a, htr458a])
            obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc127yx, htr012a, htr017c, htr078a, htr178a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr358a, htr358b, htr358c, _, _⟩
              linarith only [hlam, htr345b, htr358a, htr458a])
            obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hc124yx, hc789xy, htr012a, htr017a, htr145a, htr178a, htr457a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc567xy, htr127b, htr179a, htr256a, htr257b, htr579a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hd12b, hd89a, htr012a, htr015a, htr158a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hc578yx, htr357a, htr358c, htr389a, htr589a])
            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
            rcases m.htr 6 8 9 (by decide) (by decide) with
              ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
            ·
              linarith only [hlam, hc124yx, hc789yz, htr012a, htr014b, htr017a, htr046a, htr179a, htr468a, htr689a]
            ·
              linarith only [hlam, hc123yx, hc568yz, htr012a, htr013b, htr015a, htr038a, htr158a, htr389a, htr689a]
        ·
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr012a, htr015a, htr125b, htr257a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hd12b, hd57a, htr012a, htr017a, htr178a, htr578a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc234yz, htr126b, htr167b, htr178a, htr246b, htr347a, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd12b, hd79a, htr012a, htr015a, htr125b, htr257a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hd12b, hd57a, htr012a, htr017a, htr179a, htr579a])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc234yz, htr126b, htr167b, htr179a, htr246b, htr347a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hc124yx, hc567yz, htr012a, htr014b, htr015a, htr047a, htr125b, htr257a, htr478a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc124yx, hc578yz, htr012a, htr014b, htr015a, htr046a, htr158a, htr467a, htr678a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc124yx, hc567yz, htr012a, htr014b, htr015a, htr047a, htr125b, htr257a, htr479a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc124yx, hc789zy, htr012a, htr014b, htr018a, htr046a, htr189a, htr467a, htr679a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc568xy, htr156a, htr158b, htr189a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd24a, hd89b, htr246a, htr467a, htr678a, htr789a]
          ·
            linarith only [hlam, hd56a, hd78b, htr156a, htr158a, htr589a, htr789a]
  ·
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567xy, htr124b, htr145a, htr246a, htr456b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc234yz, htr125b, htr157a, htr245b, htr345a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568xy, htr124b, htr145a, htr246a, htr456b, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc234yz, htr125b, htr158a, htr245b, htr345a, htr458a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hc569xy, htr124b, htr145a, htr246a, htr456b, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr159a, htr159b, htr159c, _, _⟩
      linarith only [hlam, hc234yz, htr125b, htr159a, htr245b, htr345a, htr459a])
    obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd12b, hd78a, htr012a, htr015a, htr157a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd12b, hd57a, htr012a, htr017a, htr178a, htr578a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd12b, hd89a, htr012a, htr015a, htr158a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc123yx, hc578yz, htr012a, htr013b, htr015a, htr036a, htr158a, htr367a, htr678a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc126yx, hc568yz, htr012a, htr015a, htr158a, htr167a, htr367a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc356zy, htr368a, htr568b, htr589a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc126yx, hc589yz, htr012a, htr015a, htr159a, htr167a, htr678a, htr789a]
      ·
        linarith only [hlam, hc126yx, hc578yz, htr012a, htr015a, htr158a, htr168a, htr689a, htr789a]
    ·
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc126yx, hc567yz, htr012a, htr015a, htr157a, htr168a, htr367a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc123yx, hc589yz, htr012a, htr013b, htr015a, htr036a, htr159a, htr368a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc127yx, hc568yz, htr012a, htr015a, htr158a, htr178a, htr689a, htr789a]
      ·
        linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]

theorem shard_308 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr038a : m.d 0 3 + lam ≤ m.d 3 8)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False :=
  proof_shard_308 m htr012a htr013b htr014b htr015a htr016a htr016c htr017a htr017c htr018a htr018c htr025b htr036a htr038a htr045a htr045c htr124b htr125b htr126b htr127b htr145a htr245a htr245b htr345a htr345b htr345c htr456a htr456b htr456c

#print axioms shard_308
end Jsp404.NoSatElevenDBMTerminal
