import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_356 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd15a := (m.hrange 1 5 (by decide)).1
  have hd17a := (m.hrange 1 7 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
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
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd510a := (m.hrange 5 10 (by decide)).1
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
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  rcases m.htr 2 4 6 (by decide) (by decide) with
    ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
  ·
    rcases m.htr 2 4 7 (by decide) (by decide) with
      ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
    ·
      rcases m.htr 2 4 8 (by decide) (by decide) with
        ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
      ·
        rcases m.htr 2 4 9 (by decide) (by decide) with
          ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
        ·
          rcases m.htr 2 4 10 (by decide) (by decide) with
            ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
          ·
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc123xy, hc567yx, htr013a, htr015a, htr124a, htr157a, htr245a, htr456a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, hc123xy, hc568yx, htr013a, htr015a, htr124a, htr158a, htr245a, htr456a])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd12a, hd67b, htr124a, htr245a, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd12a, hd68b, htr124a, htr245a, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc123xy, hc567zy, htr013a, htr016a, htr124a, htr167a, htr245a, htr457a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd12a, hd78b, htr124a, htr245a, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd12a, hd79b, htr124a, htr245a, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc156yz, htr167a, htr567c, htr578a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc156yz, htr167b, htr178a, htr567a, htr678a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                  linarith only [hlam, hc123xy, hc578zy, htr013a, htr017a, htr124a, htr178a, htr245a, htr458a])
                obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc156yz, htr167a, htr567c, htr579a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc156yz, htr167b, htr179a, htr567a, htr679a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc123xy, hc789yz, htr013a, htr017a, htr124a, htr179a, htr248a, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc135yx, hc478zy, htr013a, htr017a, htr158a, htr178a, htr489a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a]
                ·
                  linarith only [hlam, hd13b, hd89a, htr013a, htr017a, htr178a, htr789a]
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc156yz, htr167a, htr456a, htr457a, htr567b])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hd12a, hd56b, htr125a, htr257a, htr456a, htr457a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr578a, htr678a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr124a, htr168a, htr247a, htr478a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc123xy, hc789yx, htr013a, htr017a, htr124a, htr179a, htr247a, htr478a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                  linarith only [hlam, hc156yz, htr168a, htr245c, htr258a, htr456a, htr568b])
                obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd17a, hd56b, htr179a, htr456a, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc567yx, htr456a, htr457c, htr479a, htr579a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc123xy, hc789zy, htr013a, htr018a, htr124a, htr189a, htr247a, htr479a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd15a, hd89b, htr157a, htr257a, htr258a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 6 8 9 (by decide) (by decide) with
                  ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                ·
                  linarith only [hlam, hc156yz, htr168a, htr568c, htr589a, htr689a]
                ·
                  linarith only [hlam, hc156yz, htr168b, htr189a, htr568a, htr689a]
            ·
              rcases m.htr 3 5 6 (by decide) (by decide) with
                ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
              ·
                have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                  linarith only [hlam, hd13b, hd35a, htr013a, htr015a, htr156a, htr356a])
                obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc135yx, htr013a, htr015c, htr056a, htr156a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                rcases m.htr 2 5 6 (by decide) (by decide) with
                  ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
                ·
                  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                    linarith only [hlam, hd12a, hd57b, htr125a, htr256a, htr456a, htr457a])
                  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                  rcases m.htr 3 5 7 (by decide) (by decide) with
                    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hc345yz, htr056a, htr057a, htr357a, htr456a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                      linarith only [hlam, hc345yz, htr256a, htr257a, htr357a, htr456a])
                    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                    rcases m.htr 3 5 8 (by decide) (by decide) with
                      ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
                    ·
                      rcases m.htr 3 5 9 (by decide) (by decide) with
                        ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
                      ·
                        rcases m.htr 3 5 10 (by decide) (by decide) with
                          ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                        ·
                          rcases m.htr 5 6 7 (by decide) (by decide) with
                            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                          ·
                            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                              linarith only [hlam, hc123xy, hc678yx, htr013a, htr016a, htr125a, htr168a, htr256a, htr567a])
                            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                              linarith only [hlam, hc345yz, htr136b, htr168a, htr256c, htr268a, htr356b, htr456a])
                            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                              linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                              linarith only [hlam, hd12a, hd67b, htr126a, htr268a, htr467a, htr468a])
                            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc123xy, hc678zy, htr013a, htr017a, htr124a, htr178a, htr246a, htr468a])
                            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                              linarith only [hlam, hc345yz, htr137b, htr178a, htr357b, htr457a, htr578a])
                            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd12a, hd78b, htr125a, htr256a, htr567a, htr678a]
                            ·
                              linarith only [hlam, hd12a, hd67b, htr125a, htr257a, htr578a, htr678a]
                          ·
                            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                              linarith only [hlam, hc345yz, htr136b, htr167a, htr356b, htr456a, htr567a])
                            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                              linarith only [hlam, hc123xy, hc678xy, htr013a, htr016a, htr125a, htr167a, htr256a, htr568a])
                            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                              linarith only [hlam, hc345yz, htr136b, htr168a, htr356b, htr456a, htr568a])
                            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                              linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr124a, htr168a, htr247a, htr478a])
                            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                              linarith only [hlam, hc123xy, hc467zy, htr013a, htr016a, htr127a, htr167a, htr278a, htr478a])
                            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc345yz, htr137b, htr178a, htr257c, htr278a, htr357b, htr457a])
                            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a]
                            ·
                              linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a]
                        ·
                          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                            linarith only [hlam, htr035b, htr0510a, htr3510a])
                          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                            linarith only [hlam, htr0510c, htr056b, htr0610b])
                          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                            linarith only [hlam, htr0510c, htr057b, htr0710b])
                          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                          have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                            linarith only [hlam, hc136yx, htr013a, htr016c, htr0610a, htr1610a])
                          obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
                          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                            linarith only [hlam, hc137yx, htr013a, htr017c, htr0710a, htr1710a])
                          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                            linarith only [hlam, hc123xy, hc6710yx, htr013a, htr016a, htr125a, htr1610a, htr256a, htr567a])
                          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                            linarith only [hlam, hc345yz, htr136b, htr167a, htr356b, htr456a, htr567a])
                          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                          rcases m.htr 6 7 10 (by decide) (by decide) with
                            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                          ·
                            linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr1710a, htr6710a]
                          ·
                            linarith only [hlam, hd13b, hd710a, htr013a, htr016a, htr167a, htr6710a]
                      ·
                        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                          linarith only [hlam, htr035b, htr059a, htr359a])
                        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                          linarith only [hlam, htr056b, htr059c, htr069b])
                        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, htr057b, htr059c, htr079b])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                          linarith only [hlam, hc136yx, htr013a, htr016c, htr069a, htr169a])
                        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc137yx, htr013a, htr017c, htr079a, htr179a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc123xy, hc679yx, htr013a, htr016a, htr125a, htr169a, htr256a, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                          linarith only [hlam, hc345yz, htr136b, htr167a, htr356b, htr456a, htr567a])
                        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                        rcases m.htr 6 7 9 (by decide) (by decide) with
                          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                        ·
                          linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr179a, htr679a]
                        ·
                          linarith only [hlam, hd13b, hd79a, htr013a, htr016a, htr167a, htr679a]
                    ·
                      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                        linarith only [hlam, htr035b, htr058a, htr358a])
                      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                        linarith only [hlam, htr056b, htr058c, htr068b])
                      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, htr057b, htr058c, htr078b])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                        linarith only [hlam, hc136yx, htr013a, htr016c, htr068a, htr168a])
                      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                        linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
                      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc123xy, hc678yx, htr013a, htr016a, htr125a, htr168a, htr256a, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                        linarith only [hlam, hc345yz, htr136b, htr167a, htr356b, htr456a, htr567a])
                      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a]
                      ·
                        linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a]
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, htr035b, htr057a, htr357a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                      linarith only [hlam, htr056b, htr057c, htr067b])
                    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                      linarith only [hlam, hc136yx, htr013a, htr016c, htr067a, htr167a])
                    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                      linarith only [hlam, htr125c, htr135b, htr257a, htr357a])
                    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc123xy, hc678xy, htr013a, htr016a, htr125a, htr167a, htr256a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc345yz, htr136b, htr168a, htr356b, htr456a, htr568a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr124a, htr168a, htr247a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc123xy, hc457zy, htr013a, htr015a, htr127a, htr135b, htr278a, htr357a, htr478a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd45b, hd67a, htr256a, htr257c, htr278a, htr456a, htr678a]
                    ·
                      linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a]
                ·
                  rcases m.htr 5 6 7 (by decide) (by decide) with
                    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                  ·
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc345yz, htr356a, htr456c, htr467a, htr567a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc123xy, hc678yx, htr013a, htr016a, htr124a, htr168a, htr246a, htr467a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                      linarith only [hlam, hc123xy, hc679yx, htr013a, htr016a, htr124a, htr169a, htr246a, htr467a])
                    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc345yz, htr136b, htr168a, htr356b, htr456a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc123xy, hc678zy, htr013a, htr017a, htr124a, htr178a, htr246a, htr468a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc345yz, htr136b, htr169a, htr356b, htr456a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                      linarith only [hlam, hc345yz, htr356a, htr456c, htr469a, htr569a])
                    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc123xy, hc689zy, htr013a, htr018a, htr124a, htr189a, htr246a, htr469a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd12a, hd78b, htr124a, htr246a, htr467a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd12a, hd89b, htr124a, htr246a, htr468a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc167yz, htr178a, htr678c, htr689a, htr789a]
                    ·
                      linarith only [hlam, hc167yz, htr178b, htr189a, htr678a, htr789a]
                  ·
                    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                      linarith only [hlam, hc345yz, htr136b, htr167a, htr356b, htr456a, htr567a])
                    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc123xy, hc678xy, htr013a, htr016a, htr124a, htr167a, htr246a, htr468a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                      linarith only [hlam, hc123xy, hc679xy, htr013a, htr016a, htr124a, htr167a, htr246a, htr469a])
                    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc345yz, htr356a, htr456c, htr468a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc345yz, htr136b, htr168a, htr356b, htr456a, htr568a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr124a, htr168a, htr247a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc345yz, htr356a, htr456c, htr469a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                      linarith only [hlam, hc345yz, htr136b, htr169a, htr356b, htr456a, htr569a])
                    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hc123xy, hc689yz, htr013a, htr016a, htr124a, htr169a, htr248a, htr489a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd13b, hd89a, htr013a, htr016a, htr168a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a]
                    ·
                      linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a]
              ·
                have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                  linarith only [hlam, hc123xy, hc567xy, htr013a, htr015a, htr124a, htr135b, htr245a, htr356a, htr457a])
                obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd13b, hd67a, htr013a, htr015a, htr135b, htr356a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd13b, hd68a, htr013a, htr015a, htr135b, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hd13b, hd56a, htr013a, htr016a, htr168a, htr568a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                rcases m.htr 4 6 7 (by decide) (by decide) with
                  ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                ·
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hc123xy, hc567yz, htr013a, htr015a, htr124a, htr157a, htr246a, htr467a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hc135yx, htr013a, htr015c, htr057a, htr157a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd12a, hd78b, htr124a, htr246a, htr467a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd56a, hd67b, htr135b, htr157a, htr356a, htr578a, htr678a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hc567xy, htr135b, htr157b, htr178a, htr356a, htr578a])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hc123xy, hc678zy, htr013a, htr017a, htr124a, htr178a, htr246a, htr468a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hc456zy, htr035b, htr058a, htr356a, htr468a, htr568c])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc789xy, htr057a, htr058a, htr578b, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc567xy, htr135b, htr157b, htr179a, htr356a, htr579a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc123xy, hc789yz, htr013a, htr017a, htr124a, htr179a, htr248a, htr489a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd45b, hd89a, htr057a, htr058a, htr457a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 6 8 9 (by decide) (by decide) with
                    ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                  ·
                    linarith only [hlam, hc136yx, hc478zy, htr013a, htr017a, htr168a, htr178a, htr489a, htr689a]
                  ·
                    linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a]
                ·
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hc456zy, htr135b, htr157a, htr356a, htr467a, htr567c])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd13b, hd78a, htr013a, htr015a, htr157a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd13b, hd79a, htr013a, htr015a, htr157a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, hc123xy, hc578yz, htr013a, htr015a, htr124a, htr158a, htr247a, htr478a])
                  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456zy, htr467a, htr567b, htr579a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc123xy, hc789zy, htr013a, htr018a, htr124a, htr189a, htr247a, htr479a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc568xy, htr135b, htr158b, htr189a, htr356a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd12a, hd89b, htr124a, htr247a, htr478a, htr789a]
                  ·
                    linarith only [hlam, hd56a, hd78b, htr135b, htr158a, htr356a, htr589a, htr789a]
          ·
            have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
              linarith only [hlam, htr2410c, htr245b, htr2510b])
            obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
            have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
              linarith only [hlam, htr2410c, htr246b, htr2610b])
            obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
            have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
              linarith only [hlam, htr245c, htr2510a, htr4510a])
            obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
            have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
              linarith only [hlam, hc145yz, htr1510a, htr2410a, htr245a, htr4510b])
            obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hc5610yx, htr2410a, htr245a, htr4510b, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, htr246c, htr2610a, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
              linarith only [hlam, hc146yz, htr1610a, htr2410a, htr246a, htr4610b])
            obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc6710yx, htr2410a, htr246a, htr4610b, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              linarith only [hlam, hc456zy, htr2410a, htr246a, htr4610b, htr5610a])
            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hd13b, hd610a, htr013a, htr015a, htr156a, htr5610a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc135yx, htr013a, htr015c, htr056a, htr156a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, hc4510yx, htr0410a, htr045b, htr056a, htr456a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc123xy, hc467zy, htr012b, htr013a, htr016a, htr024b, htr0410a, htr167a, htr2410a, htr247a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              linarith only [hlam, hd46b, hd510a, htr1510a, htr156a, htr467a, htr567a]
            ·
              linarith only [hlam, hd45b, hd610a, htr1610a, htr167a, htr456a, htr567a]
        ·
          have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr259a, htr259b, htr259c, _, _⟩
            linarith only [hlam, htr245b, htr249c, htr259b])
          obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
          have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr269a, htr269b, htr269c, _, _⟩
            linarith only [hlam, htr246b, htr249c, htr269b])
          obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, htr245c, htr259a, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr159a, htr159b, htr159c, _, _⟩
            linarith only [hlam, hc145yz, htr159a, htr245a, htr249a, htr459b])
          obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
          have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr456a, htr456b, htr456c, _, _⟩
            linarith only [hlam, hc569yx, htr245a, htr249a, htr456a, htr459b])
          obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, htr246c, htr269a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hc146yz, htr169a, htr246a, htr249a, htr469b])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc679yx, htr246a, htr249a, htr467a, htr469b])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc456zy, htr246a, htr249a, htr469b, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hd13b, hd69a, htr013a, htr015a, htr156a, htr569a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc135yx, htr013a, htr015c, htr056a, htr156a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc459yx, htr045b, htr049a, htr056a, htr456a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc123xy, hc467zy, htr012b, htr013a, htr016a, htr024b, htr049a, htr167a, htr247a, htr249a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            linarith only [hlam, hd46b, hd59a, htr156a, htr159a, htr467a, htr567a]
          ·
            linarith only [hlam, hd45b, hd69a, htr167a, htr169a, htr456a, htr567a]
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr245b, htr248c, htr258b])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr246b, htr248c, htr268b])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, htr245c, htr258a, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc145yz, htr158a, htr245a, htr248a, htr458b])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr456a, htr456b, htr456c, _, _⟩
          linarith only [hlam, hc568yx, htr245a, htr248a, htr456a, htr458b])
        obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr246c, htr268a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc146yz, htr168a, htr246a, htr248a, htr468b])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc678yx, htr246a, htr248a, htr467a, htr468b])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc456zy, htr246a, htr248a, htr468b, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hd13b, hd68a, htr013a, htr015a, htr156a, htr568a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc135yx, htr013a, htr015c, htr056a, htr156a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc458yx, htr045b, htr048a, htr056a, htr456a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc123xy, hc467zy, htr012b, htr013a, htr016a, htr024b, htr048a, htr167a, htr247a, htr248a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          linarith only [hlam, hd46b, hd58a, htr156a, htr158a, htr467a, htr567a]
        ·
          linarith only [hlam, hd45b, hd68a, htr167a, htr168a, htr456a, htr567a]
    ·
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr245b, htr247c, htr257b])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, htr246b, htr247c, htr267b])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, htr245c, htr257a, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc145yz, htr157a, htr245a, htr247a, htr457b])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc567yx, htr245a, htr247a, htr456a, htr457b])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc578xy, htr245a, htr247a, htr457b, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, htr246c, htr267a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc146yz, htr167a, htr246a, htr247a, htr467b])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc678xy, htr246a, htr247a, htr467b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc679xy, htr246a, htr247a, htr467b, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc456zy, htr246a, htr247a, htr467b, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hd13b, hd67a, htr013a, htr015a, htr156a, htr567a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc135yx, htr013a, htr015c, htr056a, htr156a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc458yx, htr047a, htr048a, htr245a, htr247a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hd46b, hd57a, htr156a, htr157a, htr468a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr167a, htr168a, htr456a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc123xy, hc468zy, htr012b, htr013a, htr016a, htr024b, htr047a, htr168a, htr247a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc045yz, htr058a, htr245a, htr248a, htr458b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hd46b, hd57a, htr156a, htr157a, htr469a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hd45b, hd67a, htr167a, htr169a, htr456a, htr569a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr013a, htr015a, htr157a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd45b, hd57a, htr245a, htr247a, htr478a, htr578a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd45b, hd89a, htr056a, htr058a, htr456a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd45b, hd58a, htr245a, htr248a, htr489a, htr589a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc123xy, hc689yz, htr012b, htr013a, htr016a, htr024b, htr047a, htr169a, htr478a, htr789a]
      ·
        linarith only [hlam, hc123xy, hc678yz, htr012b, htr013a, htr016a, htr024b, htr048a, htr168a, htr489a, htr789a]
  ·
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, htr245b, htr246c, htr256b])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, htr245c, htr256a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc145yz, htr156a, htr245a, htr246a, htr456b])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc345yz, htr245a, htr246a, htr356a, htr456b])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567xy, htr245a, htr246a, htr456b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc456yx, htr245b, htr246a, htr257a, htr457a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568xy, htr245a, htr246a, htr456b, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hd13b, hd67a, htr013a, htr015a, htr156a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd45b, hd56a, htr245a, htr246a, htr467a, htr567a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc456yx, htr245a, htr246c, htr267a, htr467a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd13b, hd68a, htr013a, htr015a, htr156a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd45b, hd56a, htr245a, htr246a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc456yx, htr245a, htr246c, htr268a, htr468a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr146a, htr146b, htr146c, _, _⟩
        linarith only [hlam, hd13b, hd34a, htr013a, htr014a, htr146a, htr346a])
      obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
      rcases m.htr 3 5 7 (by decide) (by decide) with
        ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
      ·
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hd13b, hd56a, htr013a, htr015c, htr057a, htr356a, htr357a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc345yz, htr245a, htr247a, htr357a, htr457b])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd34a, hd78b, htr246a, htr247a, htr346a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd34a, hd79b, htr246a, htr247a, htr346a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd47b, hd56a, htr356a, htr357a, htr478a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc567xy, htr137b, htr178a, htr356a, htr357b, htr578a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc134yx, hc478zy, htr013a, htr017a, htr146a, htr178a, htr246a, htr248a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc045yz, htr058a, htr245a, htr248a, htr458b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd47b, hd56a, htr356a, htr357a, htr479a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc567xy, htr137b, htr179a, htr356a, htr357b, htr579a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45b, hd89a, htr057a, htr058a, htr457a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd45b, hd58a, htr245a, htr248a, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc123xy, hc789yz, htr013a, htr017a, htr126a, htr179a, htr268a, htr689a]
        ·
          linarith only [hlam, hc134yx, hc678zy, htr013a, htr017a, htr146a, htr178a, htr468b, htr489a, htr689a]
      ·
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc134yx, hc457zy, htr013a, htr015a, htr135b, htr146a, htr246a, htr247a, htr357a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd13b, hd78a, htr013a, htr015a, htr135b, htr357a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd45b, hd57a, htr245a, htr247a, htr478a, htr578a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd13b, hd79a, htr013a, htr015a, htr135b, htr357a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd45b, hd57a, htr245a, htr247a, htr479a, htr579a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc134yx, hc567yz, htr013a, htr015a, htr135b, htr146a, htr357a, htr467b, htr478a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc123xy, hc578yz, htr013a, htr015a, htr126a, htr158a, htr267a, htr678a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc145yz, htr158a, htr245a, htr248a, htr458b])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd34a, hd89b, htr246a, htr248a, htr346a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd48b, hd56a, htr156a, htr158a, htr489a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc568xy, htr156a, htr158b, htr189a, htr589a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc123xy, hc789zy, htr013a, htr018a, htr126a, htr189a, htr267a, htr679a]
        ·
          linarith only [hlam, hc134yx, hc567yz, htr013a, htr015a, htr135b, htr146a, htr357a, htr467b, htr479a, htr679a]
    ·
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc456yx, htr135b, htr157a, htr345b, htr346a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc456yx, htr135b, htr158a, htr345b, htr346a, htr458a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr013a, htr015a, htr157a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hd13b, hd57a, htr013a, htr017a, htr178a, htr578a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc123xy, hc578yz, htr013a, htr015a, htr126a, htr158a, htr267a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc123xy, hc567yz, htr013a, htr015a, htr127a, htr157a, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc456yx, htr034b, htr047b, htr078a, htr245c, htr257c, htr278a, htr346a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      rcases m.htr 2 4 7 (by decide) (by decide) with
        ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
      ·
        linarith only [hlam, htr024c, htr047a, htr247a]
      ·
        linarith only [hlam, hc137yx, hc456yx, htr013a, htr014a, htr134b, htr178a, htr245a, htr247c, htr278a, htr346a]

theorem shard_356 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    : False :=
  proof_shard_356 m htr012b htr013a htr014a htr015a htr015c htr016a htr016c htr017a htr017c htr018a htr024b htr024c htr034b htr035b htr045b htr124a htr125a htr125c htr126a htr127a htr134b htr135b htr136b htr137b htr245a htr245b htr245c htr345b

#print axioms shard_356
end Jsp404.NoSatElevenDBMTerminal
