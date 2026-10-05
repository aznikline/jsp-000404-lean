import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_137 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  obtain ⟨hd48a, hd48braw⟩ := m.hrange 4 8 (by decide)
  have hd48b : m.d 4 8 < 4*lam := by
    linarith only [hd48braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
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
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc369xy, hc369yx, hc369yz, hc369zy⟩ := endpoint_caps m 3 6 9 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr014c, htr045a, htr145a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hd01a, hd46b, htr014a, htr145a, htr345a, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hd01a, hd47b, htr014a, htr145a, htr345a, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hd01a, hd48b, htr014a, htr145a, htr345a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  rcases m.htr 2 4 6 (by decide) (by decide) with
    ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc234yz, htr014c, htr046a, htr145a, htr246a, htr345a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hc234yz, htr145a, htr146a, htr246a, htr345a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    rcases m.htr 2 4 7 (by decide) (by decide) with
      ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc234yz, htr014c, htr047a, htr145a, htr247a, htr345a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc234yz, htr145a, htr147a, htr247a, htr345a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      rcases m.htr 2 4 8 (by decide) (by decide) with
        ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
      ·
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc234yz, htr145a, htr148a, htr248a, htr345a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        rcases m.htr 2 4 9 (by decide) (by decide) with
          ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
        ·
          rcases m.htr 2 4 10 (by decide) (by decide) with
            ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
          ·
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hc234yz, htr245a, htr345c, htr356a, htr456a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd01a, hd67b, htr014a, htr145a, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd01a, hd56b, htr014a, htr146a, htr467a, htr567a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hc234yz, htr246b, htr267a, htr346a, htr467a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd01a, hd68b, htr014a, htr145a, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd01a, hd56b, htr014a, htr146a, htr468a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc234yz, htr246b, htr268a, htr346a, htr468a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd01a, hd78b, htr014a, htr145a, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd01a, hd57b, htr014a, htr147a, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc234yz, htr247b, htr278a, htr347a, htr478a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd01a, hd79b, htr014a, htr145a, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hd01a, hd57b, htr014a, htr147a, htr479a, htr579a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, hc234yz, htr247b, htr279a, htr347a, htr479a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc012xy, hc567zy, htr014a, htr027a, htr145a, htr278a, htr457a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                  linarith only [hlam, hc012xy, hc578zy, htr013a, htr026a, htr135a, htr267a, htr358a, htr678a])
                obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc012xy, hc567zy, htr014a, htr027a, htr145a, htr279a, htr457a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc012xy, hc789yz, htr013a, htr026a, htr138a, htr267a, htr389a, htr679a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc568yx, htr356a, htr358c, htr389a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd56b, hd78a, htr356a, htr358a, htr589a, htr789a]
                ·
                  linarith only [hlam, hd34b, hd89a, htr346a, htr467a, htr678a, htr789a]
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc234yz, htr025b, htr057a, htr245b, htr345a, htr457a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hc234yz, htr245b, htr257a, htr345a, htr457a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, htr345b, htr357a, htr457a])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                rcases m.htr 4 5 8 (by decide) (by decide) with
                  ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                ·
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, htr015c, htr058a, htr145c, htr458a])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, htr057c, htr058b, htr078c])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, htr245c, htr258a, htr458a])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc567yx, htr057b, htr078a, htr356a, htr357c, htr378a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc012xy, hc789yx, htr013a, htr025a, htr137a, htr257a, htr378a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                    linarith only [hlam, hc567yx, htr356a, htr357c, htr379a, htr579a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd01a, hd89b, htr014a, htr145a, htr458a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc578xy, htr257a, htr258b, htr289a, htr589a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  rcases m.htr 6 8 9 (by decide) (by decide) with
                    ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                  ·
                    linarith only [hlam, hc012xy, hc568zy, htr014a, htr028a, htr145a, htr289a, htr458a, htr689a]
                  ·
                    linarith only [hlam, hc012xy, hc789zy, htr013a, htr026a, htr137a, htr268a, htr379a, htr689a]
                ·
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hc567yx, htr057a, htr058a, htr456a, htr458a])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, hc567yx, htr257a, htr258a, htr456a, htr458a])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                    linarith only [hlam, htr345b, htr358a, htr458a])
                  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                  rcases m.htr 4 5 9 (by decide) (by decide) with
                    ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
                  ·
                    have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                      linarith only [hlam, htr015c, htr059a, htr145c, htr459a])
                    obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, htr057c, htr059b, htr079c])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr058c, htr059b, htr089c])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, hc567yx, htr057b, htr079a, htr356a, htr357c, htr379a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                    have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                      linarith only [hlam, hc568yx, htr058b, htr089a, htr356a, htr358c, htr389a])
                    obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hc012xy, hc789xy, htr013a, htr025a, htr137a, htr257a, htr379a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc567yx, htr356a, htr357c, htr378a, htr578a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd01a, hd89b, htr013a, htr137a, htr378a, htr789a]
                    ·
                      linarith only [hlam, hd01a, hd78b, htr013a, htr138a, htr389a, htr789a]
                  ·
                    rcases m.htr 4 5 10 (by decide) (by decide) with
                      ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                    ·
                      have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                        linarith only [hlam, htr015c, htr0510a, htr145c, htr4510a])
                      obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, htr0510b, htr057c, htr0710c])
                      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, htr0510b, htr058c, htr0810c])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                        linarith only [hlam, hc567yx, htr057b, htr0710a, htr356a, htr357c, htr3710a])
                      obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                      have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                        linarith only [hlam, hc568yx, htr058b, htr0810a, htr356a, htr358c, htr3810a])
                      obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc012xy, hc7810xy, htr013a, htr025a, htr137a, htr257a, htr3710a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc567yx, htr356a, htr357c, htr378a, htr578a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      rcases m.htr 7 8 10 (by decide) (by decide) with
                        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      ·
                        linarith only [hlam, hd01a, hd810b, htr013a, htr137a, htr378a, htr7810a]
                      ·
                        linarith only [hlam, hd01a, hd78b, htr013a, htr138a, htr3810a, htr7810a]
                    ·
                      rcases m.htr 4 7 8 (by decide) (by decide) with
                        ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                      ·
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hc012xy, hc789yx, htr014a, htr025a, htr147a, htr257a, htr478a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc567yx, htr356a, htr357c, htr379a, htr579a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc012xy, hc789zy, htr013a, htr025a, htr137a, htr258a, htr379a, htr589a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                          linarith only [hlam, hc568yx, htr356a, htr358c, htr389a, htr589a])
                        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd01a, hd89b, htr014a, htr147a, htr478a, htr789a]
                        ·
                          linarith only [hlam, hd01a, hd78b, htr013a, htr138a, htr389a, htr789a]
                      ·
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc012xy, hc789xy, htr013a, htr025a, htr137a, htr257a, htr379a, htr578a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hc567yx, htr356a, htr357c, htr379a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                          linarith only [hlam, hc012xy, hc789yz, htr013a, htr025a, htr138a, htr257a, htr389a, htr579a])
                        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc568yx, htr356a, htr358c, htr389a, htr589a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd34b, hd78a, htr345a, htr458a, htr589a, htr789a]
                        ·
                          linarith only [hlam, hd34b, hd89a, htr345a, htr457a, htr578a, htr789a]
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc234yz, htr025b, htr056a, htr245b, htr345a, htr456a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hc234yz, htr245b, htr256a, htr345a, htr456a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, htr345b, htr356a, htr456a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, htr015c, htr057a, htr145c, htr457a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, htr056c, htr057b, htr067c])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, htr245c, htr257a, htr457a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, hc234yz, htr245a, htr345c, htr357a, htr457a])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc567xy, htr056b, htr067a, htr356c, htr357a, htr367a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc012xy, hc678yx, htr013a, htr025a, htr136a, htr256a, htr367a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc567xy, htr356c, htr357a, htr368a, htr568a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hc012xy, hc679yx, htr013a, htr025a, htr136a, htr256a, htr367a, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                  linarith only [hlam, hc567xy, htr356c, htr357a, htr369a, htr569a])
                obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd01a, hd78b, htr014a, htr145a, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc567xy, htr256a, htr257b, htr278a, htr578a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd01a, hd89b, htr013a, htr136a, htr368a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hd01a, hd68b, htr014a, htr148a, htr489a, htr689a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hc234yz, htr248b, htr289a, htr348a, htr489a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hc012xy, hc678zy, htr013a, htr028a, htr136a, htr289a, htr368a, htr789a]
                ·
                  linarith only [hlam, hc012xy, hc689zy, htr013a, htr027a, htr136a, htr278a, htr369a, htr789a]
              ·
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hc234yz, htr245b, htr257a, htr345a, htr457a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                rcases m.htr 4 6 7 (by decide) (by decide) with
                  ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                ·
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, htr046c, htr067a, htr467a])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                    linarith only [hlam, hc234yz, htr246a, htr346c, htr367a, htr467a])
                  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd01a, hd78b, htr014a, htr146a, htr467a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hd01a, hd67b, htr014a, htr147a, htr478a, htr678a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc234yz, htr247b, htr278a, htr347a, htr478a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc012xy, hc567yz, htr014a, htr027a, htr146a, htr278a, htr467a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hc012xy, hc678zy, htr013a, htr025a, htr136a, htr257a, htr368a, htr578a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr367a, htr368a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc234yz, htr026b, htr068a, htr146c, htr168a, htr246b, htr346a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                    linarith only [hlam, hc012xy, hc789xy, htr013a, htr025a, htr137a, htr257a, htr379a, htr578a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, hc678yx, htr067b, htr068a, htr079a, htr367c, htr379a])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd34b, hd78a, htr047c, htr079a, htr347a, htr578a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                    linarith only [hlam, hc012xy, hc789yz, htr013a, htr025a, htr138a, htr257a, htr389a, htr579a])
                  obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc678yx, htr367a, htr368c, htr389a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd67b, hd78a, htr367a, htr368a, htr689a, htr789a]
                  ·
                    linarith only [hlam, hd34b, hd89a, htr345a, htr457a, htr578a, htr789a]
                ·
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, hc234yz, htr026b, htr067a, htr246b, htr346a, htr467a])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                    linarith only [hlam, hc234yz, htr246b, htr267a, htr346a, htr467a])
                  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                    linarith only [hlam, htr346b, htr367a, htr467a])
                  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                  rcases m.htr 5 6 7 (by decide) (by decide) with
                    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                  ·
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, hc568xy, htr056c, htr058a, htr067a, htr567a])
                    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                      linarith only [hlam, hd34b, hd56a, htr015c, htr058a, htr145c, htr256c, htr258a, htr267a, htr345a, htr567a])
                    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hd34b, hd68a, htr346a, htr467a, htr567a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    rcases m.htr 4 6 8 (by decide) (by decide) with
                      ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                    ·
                      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                        linarith only [hlam, htr046c, htr068a, htr468a])
                      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, htr067c, htr068b, htr078c])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                        linarith only [hlam, htr246c, htr268a, htr468a])
                      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc356zy, htr067b, htr078a, htr367c, htr378a, htr567a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                        linarith only [hlam, hc012xy, hc789yx, htr013a, htr026a, htr137a, htr267a, htr378a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc356zy, htr367c, htr379a, htr567a, htr679a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc012xy, hc789zy, htr013a, htr025a, htr137a, htr258a, htr379a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                        linarith only [hlam, hc012xy, hc568yz, htr014a, htr028a, htr146a, htr289a, htr468a, htr589a])
                      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd01a, hd89b, htr013a, htr137a, htr378a, htr789a]
                      ·
                        linarith only [hlam, hd56a, hd78b, htr267a, htr268b, htr289a, htr567a, htr789a]
                    ·
                      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                        linarith only [hlam, hc456zy, htr026b, htr068a, htr267a, htr468a, htr567a])
                      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                        linarith only [hlam, hc456zy, htr267a, htr268a, htr468a, htr567a])
                      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                        linarith only [hlam, htr346b, htr368a, htr468a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      rcases m.htr 4 6 9 (by decide) (by decide) with
                        ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                      ·
                        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                          linarith only [hlam, htr046c, htr069a, htr469a])
                        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, htr067c, htr069b, htr079c])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, htr068c, htr069b, htr089c])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc356zy, htr067b, htr079a, htr367c, htr379a, htr567a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                          linarith only [hlam, hc356zy, htr068b, htr089a, htr368c, htr389a, htr568a])
                        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hc012xy, hc789xy, htr013a, htr026a, htr137a, htr267a, htr379a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                          linarith only [hlam, hc356zy, htr367c, htr378a, htr567a, htr678a])
                        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd01a, hd89b, htr013a, htr137a, htr378a, htr789a]
                        ·
                          linarith only [hlam, hd01a, hd78b, htr013a, htr138a, htr389a, htr789a]
                      ·
                        rcases m.htr 4 6 10 (by decide) (by decide) with
                          ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                        ·
                          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                            linarith only [hlam, htr046c, htr0610a, htr4610a])
                          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                            linarith only [hlam, htr0610b, htr067c, htr0710c])
                          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                            linarith only [hlam, htr0610b, htr068c, htr0810c])
                          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                            linarith only [hlam, hc356zy, htr067b, htr0710a, htr367c, htr3710a, htr567a])
                          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                            linarith only [hlam, hc356zy, htr068b, htr0810a, htr368c, htr3810a, htr568a])
                          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                            linarith only [hlam, hc012xy, hc7810xy, htr013a, htr026a, htr137a, htr267a, htr3710a, htr678a])
                          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                            linarith only [hlam, hc356zy, htr367c, htr378a, htr567a, htr678a])
                          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                          rcases m.htr 7 8 10 (by decide) (by decide) with
                            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          ·
                            linarith only [hlam, hd01a, hd810b, htr013a, htr137a, htr378a, htr7810a]
                          ·
                            linarith only [hlam, hd01a, hd78b, htr013a, htr138a, htr3810a, htr7810a]
                        ·
                          rcases m.htr 6 7 8 (by decide) (by decide) with
                            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                          ·
                            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                              linarith only [hlam, hc356zy, htr367c, htr378a, htr567a, htr678a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                              linarith only [hlam, hc012xy, hc789yx, htr013a, htr026a, htr137a, htr267a, htr378a, htr679a])
                            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                              linarith only [hlam, hc356zy, htr367c, htr379a, htr567a, htr679a])
                            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                              linarith only [hlam, hc012xy, hc789zy, htr013a, htr025a, htr137a, htr258a, htr379a, htr589a])
                            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                            have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                              linarith only [hlam, hc012xy, hc578yz, htr013a, htr028a, htr137a, htr289a, htr378a, htr589a])
                            obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                              linarith only [hlam, hc356zy, htr268b, htr289a, htr368c, htr389a, htr568a])
                            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                            rcases m.htr 7 8 9 (by decide) (by decide) with
                              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                            ·
                              linarith only [hlam, hd01a, hd89b, htr013a, htr137a, htr378a, htr789a]
                            ·
                              linarith only [hlam, hd01a, hd78b, htr013a, htr138a, htr389a, htr789a]
                          ·
                            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                              linarith only [hlam, hc012xy, hc789xy, htr013a, htr026a, htr137a, htr267a, htr379a, htr678a])
                            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                              linarith only [hlam, hc356zy, htr067b, htr079a, htr367c, htr379a, htr567a])
                            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                              linarith only [hlam, hd34b, hd57a, htr346a, htr467a, htr578a, htr678a])
                            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                              linarith only [hlam, hd34b, hd78a, htr047c, htr079a, htr347a, htr578a, htr579a])
                            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                              linarith only [hlam, hc012xy, hc789yz, htr013a, htr025a, htr138a, htr257a, htr389a, htr579a])
                            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                              linarith only [hlam, hc356zy, htr368c, htr389a, htr568a, htr689a])
                            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                            rcases m.htr 7 8 9 (by decide) (by decide) with
                              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                            ·
                              linarith only [hlam, hd34b, hd78a, htr346a, htr468a, htr689a, htr789a]
                            ·
                              linarith only [hlam, hd34b, hd89a, htr346a, htr467a, htr678a, htr789a]
                  ·
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc012xy, hc678xy, htr014a, htr025a, htr146a, htr256a, htr468a, htr567a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                      linarith only [hlam, hc012xy, hc679xy, htr014a, htr025a, htr146a, htr256a, htr469a, htr567a])
                    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hd34b, hd67a, htr346a, htr468a, htr567a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc012xy, hc678yz, htr013a, htr025a, htr137a, htr256a, htr378a, htr568a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc012xy, hc367zy, htr017a, htr025a, htr178a, htr256a, htr378a, htr567a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hd34b, hd67a, htr346a, htr469a, htr567a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                      linarith only [hlam, hc012xy, hc689yz, htr013a, htr025a, htr138a, htr256a, htr389a, htr569a])
                    obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd34b, hd78a, htr345a, htr456a, htr567a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd34b, hd89a, htr345a, htr456a, htr568a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc367zy, htr378c, htr389a, htr678a, htr789a]
                    ·
                      linarith only [hlam, hd34b, hd68a, htr147c, htr178a, htr347a, htr689a, htr789a]
          ·
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, htr024b, htr0410a, htr2410a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, htr0410c, htr045b, htr0510b])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0410c, htr046b, htr0610b])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0410c, htr047b, htr0710b])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
              linarith only [hlam, htr015c, htr0510a, htr145c, htr4510a])
            obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hc5610yx, htr124b, htr145a, htr2410a, htr4510b, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, htr046c, htr0610a, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc6710yx, htr024b, htr046a, htr2410a, htr4610b, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, htr047c, htr0710a, htr4710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              linarith only [hlam, hd34b, hd56a, htr2410a, htr245a, htr345a, htr4610b, htr5610a])
            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd34b, hd610a, htr346a, htr467a, htr5610a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd34b, hd67a, htr2410a, htr245a, htr345a, htr4710b, htr6710a]
            ·
              linarith only [hlam, hd34b, hd710a, htr345a, htr456a, htr567a, htr6710a]
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, htr024b, htr049a, htr249a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr045b, htr049c, htr059b])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr046b, htr049c, htr069b])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr149a, htr149b, htr149c, _, _⟩
            linarith only [hlam, htr124b, htr149a, htr249a])
          obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, htr015c, htr059a, htr145c, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr456a, htr456b, htr456c, _, _⟩
            linarith only [hlam, hc569yx, htr124b, htr145a, htr249a, htr456a, htr459b])
          obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc234yz, htr245b, htr256a, htr345a, htr456a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, htr046c, htr069a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, hc6910xy, htr024b, htr046a, htr249a, htr4610a, htr469b])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd34b, hd910a, htr245a, htr249a, htr345a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
            linarith only [hlam, hc459yx, htr145a, htr149c, htr1910a, htr4910a])
          obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hd34b, hd56a, htr245a, htr249a, htr345a, htr469b, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hc012xy, hc369zy, htr019a, htr025a, htr1910a, htr256a, htr3910a, htr569a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 5 6 10 (by decide) (by decide) with
            ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
          ·
            linarith only [hlam, hd34b, hd69a, htr346a, htr4610a, htr5610a, htr569a]
          ·
            linarith only [hlam, hc012xy, hc6910yz, htr013a, htr025a, htr139a, htr256a, htr3910a, htr5610a]
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr024b, htr048a, htr248a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr045b, htr048c, htr058b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr046b, htr048c, htr068b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, htr124b, htr148a, htr248a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, htr015c, htr058a, htr145c, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr456a, htr456b, htr456c, _, _⟩
          linarith only [hlam, hc568yx, htr124b, htr145a, htr248a, htr456a, htr458b])
        obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc234yz, htr245b, htr256a, htr345a, htr456a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr046c, htr068a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc689xy, htr024b, htr046a, htr248a, htr468b, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd34b, hd89a, htr245a, htr248a, htr345a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc458yx, htr145a, htr148c, htr189a, htr489a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd34b, hd56a, htr245a, htr248a, htr345a, htr468b, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc012xy, hc368zy, htr018a, htr025a, htr189a, htr256a, htr389a, htr568a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 5 6 9 (by decide) (by decide) with
          ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
        ·
          linarith only [hlam, hd34b, hd68a, htr346a, htr469a, htr568a, htr569a]
        ·
          linarith only [hlam, hc012xy, hc689yz, htr013a, htr025a, htr138a, htr256a, htr389a, htr569a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr024b, htr047a, htr247a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr045b, htr047c, htr057b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr046b, htr047c, htr067b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr124b, htr147a, htr247a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, htr015c, htr057a, htr145c, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc567yx, htr124b, htr145a, htr247a, htr456a, htr457b])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc234yz, htr245b, htr256a, htr345a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, htr046c, htr067a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc678xy, htr024b, htr046a, htr247a, htr467b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd34b, hd78a, htr245a, htr247a, htr345a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc457yx, htr145a, htr147c, htr178a, htr478a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hd34b, hd56a, htr245a, htr247a, htr345a, htr467b, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc012xy, hc367zy, htr017a, htr025a, htr178a, htr256a, htr378a, htr567a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        linarith only [hlam, hd34b, hd67a, htr346a, htr468a, htr567a, htr568a]
      ·
        linarith only [hlam, hc012xy, hc678yz, htr013a, htr025a, htr137a, htr256a, htr378a, htr568a]
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, htr024b, htr046a, htr246a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, htr045b, htr046c, htr056b])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, htr124b, htr146a, htr246a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, htr015c, htr056a, htr145c, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567xy, htr124b, htr145a, htr246a, htr456b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc234yz, htr245b, htr257a, htr345a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568xy, htr124b, htr145a, htr246a, htr456b, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc234yz, htr245b, htr258a, htr345a, htr458a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd34b, hd67a, htr245a, htr246a, htr345a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc456yx, htr145a, htr146c, htr167a, htr467a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd34b, hd68a, htr245a, htr246a, htr345a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hc456yx, htr145a, htr146c, htr168a, htr468a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd34b, hd69a, htr245a, htr246a, htr345a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
      linarith only [hlam, hc456yx, htr145a, htr146c, htr169a, htr469a])
    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
    rcases m.htr 3 6 7 (by decide) (by decide) with
      ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
    ·
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr367a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hd01a, hd67b, htr016a, htr169a, htr367a, htr369a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc012xy, hc678zy, htr013a, htr025a, htr136a, htr257a, htr368a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc012xy, hc689zy, htr013a, htr025a, htr136a, htr258a, htr369a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd01a, hd78b, htr013a, htr136a, htr367a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr013a, htr136a, htr368a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
      ·
        linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc346zy, htr024b, htr047a, htr246a, htr367a, htr467c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd01a, hd68b, htr016a, htr167a, htr367a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc346zy, htr024b, htr048a, htr246a, htr368a, htr468c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd34b, hd78a, htr014c, htr047a, htr145a, htr345a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd34b, hd89a, htr014c, htr048a, htr145a, htr345a, htr489a])
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
        linarith only [hlam, hd01a, hd89b, htr016a, htr167a, htr678a, htr789a]
      ·
        linarith only [hlam, hd01a, hd78b, htr016a, htr168a, htr689a, htr789a]

theorem shard_137 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    : False :=
  proof_shard_137 m htr013a htr014a htr014c htr015c htr016a htr017a htr018a htr019a htr024b htr025a htr025b htr026a htr026b htr027a htr028a htr124b htr135a htr136a htr137a htr138a htr139a htr145a htr145c htr245a htr245b htr245c htr345a htr345b htr345c

#print axioms shard_137
end Jsp404.NoSatElevenDBMTerminal
