import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_485 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  have hd68a := (m.hrange 6 8 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd79a := (m.hrange 7 9 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  have hd810a := (m.hrange 8 10 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc234zy, htr135b, htr156a, htr245a, htr345b, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr024c, htr045a, htr246a, htr456c])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc234zy, htr245a, htr345b, htr356a, htr456a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd01b, hd67a, htr013a, htr135a, htr356a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr013a, htr136a, htr367a, htr567a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd01b, hd68a, htr013a, htr135a, htr356a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr013a, htr136a, htr368a, htr568a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hc234zy, htr145a, htr146a, htr245a, htr346a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc234zy, htr145c, htr156c, htr167a, htr245a, htr346b, htr367a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr147a, htr147b, htr147c, _, _⟩
      linarith only [hlam, htr146b, htr147c, htr167b])
    obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc234zy, htr245a, htr346b, htr367a, htr456c, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc234zy, htr246c, htr267a, htr346a, htr467a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc234zy, htr245a, htr346b, htr368a, htr456c, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc234zy, htr246c, htr268a, htr346a, htr468a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    rcases m.htr 3 5 7 (by decide) (by decide) with
      ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
    ·
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, hc234zy, htr245a, htr345b, htr357a, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc234zy, htr025c, htr057a, htr245c, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc234zy, htr245c, htr257a, htr345a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      rcases m.htr 4 5 8 (by decide) (by decide) with
        ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc567xy, htr057a, htr058a, htr456a, htr458a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc567xy, htr257a, htr258a, htr456a, htr458a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr345c, htr358a, htr458a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
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
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hc012yx, hc789yx, htr013a, htr025a, htr137a, htr257a, htr379a, htr578a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc567xy, htr356a, htr357b, htr379a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc012yx, hc789zy, htr013a, htr025a, htr138a, htr257a, htr389a, htr579a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568xy, htr356a, htr358b, htr389a, htr589a])
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
                linarith only [hlam, hc012yx, hc789xy, htr013a, htr025a, htr137a, htr257a, htr378a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hc567xy, htr356a, htr357b, htr379a, htr579a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc012yx, hc789yz, htr013a, htr025a, htr137a, htr258a, htr379a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc568xy, htr356a, htr358b, htr389a, htr589a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd01b, hd78a, htr013a, htr138a, htr389a, htr789a]
              ·
                linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a]
          ·
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, htr045b, htr0510a, htr4510a])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0510c, htr057b, htr0710b])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
              linarith only [hlam, htr0510c, htr058b, htr0810b])
            obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
            have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
              linarith only [hlam, hc567xy, htr057c, htr0710a, htr356a, htr357b, htr3710a])
            obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
            have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
              linarith only [hlam, hc568xy, htr058c, htr0810a, htr356a, htr358b, htr3810a])
            obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc012yx, hc7810yx, htr013a, htr025a, htr137a, htr257a, htr3710a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hc567xy, htr356a, htr357b, htr378a, htr578a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            rcases m.htr 7 8 10 (by decide) (by decide) with
              ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            ·
              linarith only [hlam, hd01b, hd78a, htr013a, htr138a, htr3810a, htr7810a]
            ·
              linarith only [hlam, hd01b, hd810a, htr013a, htr137a, htr378a, htr7810a]
        ·
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr045b, htr059a, htr459a])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr057b, htr059c, htr079b])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
            linarith only [hlam, htr058b, htr059c, htr089b])
          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc567xy, htr057c, htr079a, htr356a, htr357b, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc568xy, htr058c, htr089a, htr356a, htr358b, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc012yx, hc789yx, htr013a, htr025a, htr137a, htr257a, htr379a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc567xy, htr356a, htr357b, htr378a, htr578a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd01b, hd78a, htr013a, htr138a, htr389a, htr789a]
          ·
            linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a]
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr045b, htr058a, htr458a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr057b, htr058c, htr078b])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr245b, htr258a, htr458a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc567xy, htr356a, htr358a, htr457a, htr458a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc567xy, htr057c, htr078a, htr356a, htr357b, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc012yx, hc789xy, htr013a, htr025a, htr137a, htr257a, htr378a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc567xy, htr356a, htr357b, htr379a, htr579a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr013a, htr135a, htr358a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc578yx, htr257a, htr258c, htr289a, htr589a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc012yx, hc789yz, htr013a, htr026a, htr137a, htr268a, htr379a, htr689a]
        ·
          linarith only [hlam, hc012yx, hc568yz, htr013a, htr028a, htr135a, htr289a, htr358a, htr689a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc457zy, htr045a, htr047a, htr345c, htr357a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, htr024c, htr047a, htr247a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd01b, hd57a, htr013a, htr137a, htr378a, htr578a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc034zy, htr047a, htr346b, htr367b, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc124yz, htr147a, htr247c, htr278a, htr478a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd01b, hd79a, htr013a, htr135a, htr357a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hd01b, hd57a, htr013a, htr137a, htr379a, htr579a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc034zy, htr047a, htr346b, htr367b, htr379a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc124yz, htr147a, htr247c, htr279a, htr479a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc012yx, hc567yz, htr013a, htr027a, htr135a, htr278a, htr357a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc012yx, hc578yz, htr013a, htr026a, htr135a, htr267a, htr358a, htr678a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc012yx, hc567yz, htr013a, htr027a, htr135a, htr279a, htr357a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc012yx, hc789zy, htr013a, htr026a, htr138a, htr267a, htr389a, htr679a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc568xy, htr356a, htr358b, htr389a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd34a, hd89b, htr346a, htr467a, htr678a, htr789a]
      ·
        linarith only [hlam, hd56a, hd78b, htr356a, htr358a, htr589a, htr789a]
  ·
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567xy, htr134b, htr145a, htr346a, htr456b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc234zy, htr245a, htr345b, htr357a, htr457a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568xy, htr134b, htr145a, htr346a, htr456b, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc234zy, htr245a, htr345b, htr358a, htr458a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
      linarith only [hlam, hc569xy, htr134b, htr145a, htr346a, htr456b, htr459a])
    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
    have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr359a, htr359b, htr359c, _, _⟩
      linarith only [hlam, hc234zy, htr245a, htr345b, htr359a, htr459a])
    obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
    have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
      linarith only [hlam, hc5610xy, htr134b, htr145a, htr346a, htr4510a, htr456b])
    obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
    have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
      linarith only [hlam, hc234zy, htr245a, htr345b, htr3510a, htr4510a])
    obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, htr346b, htr367a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd01b, hd57a, htr013a, htr137a, htr378a, htr578a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd01b, hd79a, htr013a, htr135a, htr357a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd01b, hd89a, htr013a, htr135a, htr358a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr389a, htr389b, htr389c, _, _⟩
      linarith only [hlam, hd01b, hd58a, htr013a, htr138a, htr389a, htr589a])
    obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      linarith only [hlam, hd01b, hd910a, htr013a, htr135a, htr359a, htr5910a])
    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc246zy, htr267a, htr346a, htr347a, htr467c])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc467xy, htr346a, htr347b, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hc012yx, hc578yz, htr013a, htr026a, htr135a, htr267a, htr358a, htr678a]
      ·
        linarith only [hlam, hd46a, hd67b, htr346a, htr347a, htr478a, htr678a]
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, htr347b, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc247zy, htr278a, htr347a, htr348a, htr478c])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc468xy, htr346a, htr348b, htr389a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc012yx, hc589yz, htr013a, htr027a, htr135a, htr278a, htr359a, htr789a]
        ·
          linarith only [hlam, hd46a, hd78b, htr346a, htr348a, htr489a, htr789a]
      ·
        rcases m.htr 2 6 7 (by decide) (by decide) with
          ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
        ·
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hc012yx, hc578yz, htr013a, htr026a, htr135a, htr267a, htr358a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc567yz, htr267a, htr268a, htr578a, htr678b])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc012yx, hc589yz, htr013a, htr026a, htr135a, htr268a, htr359a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
          ·
            linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
        ·
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hc256zy, htr267a, htr567b, htr578a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc256zy, htr267c, htr278a, htr567a, htr678a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc256zy, htr267a, htr567b, htr579a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hc256zy, htr267c, htr279a, htr567a, htr679a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc012yx, hc589yz, htr013a, htr027a, htr135a, htr278a, htr359a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc012yx, hc5910yz, htr013a, htr027a, htr135a, htr279a, htr3510a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a]
          ·
            linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]

theorem shard_485 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False :=
  proof_shard_485 m htr013a htr024c htr025a htr025c htr026a htr027a htr028a htr045a htr045b htr134b htr135a htr135b htr136a htr137a htr138a htr145a htr145c htr245a htr245b htr245c htr345a htr345b htr345c htr456a htr456b htr456c

#print axioms shard_485
end Jsp404.NoSatElevenDBMTerminal
