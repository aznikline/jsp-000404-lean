import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_360 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr139c : m.d 1 9 < m.d 3 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
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
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
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
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd12a, hd56b, htr012a, htr014a, htr134c, htr345a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd12a, hd57b, htr012a, htr014a, htr134c, htr345a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hd12a, hd45b, htr012a, htr015a, htr157a, htr457a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr012a, htr014a, htr134c, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr167a, htr467a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd12a, hd68b, htr012a, htr014a, htr134c, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr168a, htr468a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd12a, hd69b, htr012a, htr014a, htr134c, htr346a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
      linarith only [hlam, hd12a, hd46b, htr012a, htr016a, htr169a, htr469a])
    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr012a, htr014a, htr134c, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd12a, hd79b, htr012a, htr014a, htr134c, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hd12a, hd47b, htr012a, htr017a, htr179a, htr479a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc456zy, htr134c, htr148a, htr346a, htr468b, htr568a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd12a, hd89b, htr012a, htr014a, htr148a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hd12a, hd810b, htr012a, htr014a, htr148a, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
            linarith only [hlam, hc456zy, htr468c, htr4810a, htr568a, htr6810a])
          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc126xy, hc478zy, htr012a, htr014a, htr148a, htr168a, htr689a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr149a, htr149b, htr149c, _, _⟩
            linarith only [hlam, hc126xy, hc489zy, htr012a, htr014a, htr149a, htr167a, htr678a, htr789a])
          obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc456zy, htr134c, htr149a, htr346a, htr469b, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd46b, hd910a, htr467a, htr567a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd45b, hd69a, htr134c, htr149a, htr345a, htr4910a, htr6910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
            linarith only [hlam, hc459yx, htr134c, htr149c, htr1910a, htr345a, htr4910a])
          obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hc126xy, hc478zy, htr012a, htr014a, htr148a, htr168a, htr6810a, htr7810a]
          ·
            linarith only [hlam, hc126xy, hc8910yz, htr012a, htr019a, htr167a, htr1910a, htr678a, htr7810a]
        ·
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc126xy, hc468zy, htr012a, htr014a, htr148a, htr167a, htr567a, htr568a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc124xy, htr012a, htr014b, htr048a, htr148a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hd46b, hd89a, htr467a, htr567a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd45b, hd68a, htr134c, htr148a, htr345a, htr489a, htr689a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc458yx, htr134c, htr148c, htr189a, htr345a, htr489a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc126xy, hc689yz, htr012a, htr018a, htr167a, htr189a, htr567a, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc456zy, htr034c, htr049a, htr346a, htr469b, htr569a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr149a, htr149b, htr149c, _, _⟩
            linarith only [hlam, hc458yx, htr048a, htr049a, htr134c, htr149a, htr345a])
          obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc8910yx, htr048a, htr049a, htr4810a, htr489c])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
            linarith only [hlam, hc458yx, htr134c, htr148c, htr1810a, htr345a, htr4810a])
          obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd12a, hd910b, htr012a, htr014a, htr149a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc456zy, htr469c, htr4910a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            linarith only [hlam, hc126xy, hc789yz, htr012a, htr018a, htr169a, htr189a, htr6910a, htr7910a]
          ·
            linarith only [hlam, hc126xy, hc8910zy, htr012a, htr018a, htr167a, htr1810a, htr679a, htr7910a]
      ·
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc126xy, hc467zy, htr012a, htr014a, htr134c, htr168a, htr347a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc126xy, hc467zy, htr012a, htr014a, htr134c, htr169a, htr347a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc467zy, htr134c, htr148a, htr347a, htr478b, htr678a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd12a, hd89b, htr012a, htr014a, htr148a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hd12a, hd810b, htr012a, htr014a, htr148a, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc467zy, htr478c, htr489a, htr678a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr149a, htr149b, htr149c, _, _⟩
            linarith only [hlam, hc125xy, hc489zy, htr012a, htr014a, htr149a, htr156a, htr568a, htr689a])
          obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc467zy, htr478c, htr4810a, htr678a, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
            linarith only [hlam, hc467zy, htr478a, htr678b, htr6810a, htr7810a])
          obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
            linarith only [hlam, hc125xy, hc8910yz, htr012a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
          obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hc459yx, htr134c, htr149c, htr1910a, htr345a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd45b, hd89a, htr134c, htr149a, htr345a, htr4910a, htr8910a]
          ·
            linarith only [hlam, hd45b, hd910a, htr456a, htr568a, htr689a, htr8910a]
        ·
          have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr148a, htr148b, htr148c, _, _⟩
            linarith only [hlam, hc125xy, hc478zy, htr012a, htr014a, htr148a, htr156a, htr567a, htr678a])
          obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, hc124xy, htr012a, htr014b, htr048a, htr148a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd45b, hd89a, htr456a, htr567a, htr678a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd45b, hd78a, htr134c, htr148a, htr345a, htr489a, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc458yx, htr134c, htr148c, htr189a, htr345a, htr489a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc125xy, hc789yz, htr012a, htr018a, htr156a, htr189a, htr567a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc467zy, htr034c, htr049a, htr347a, htr479b, htr679a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr149a, htr149b, htr149c, _, _⟩
            linarith only [hlam, hc458yx, htr048a, htr049a, htr134c, htr149a, htr345a])
          obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc8910yx, htr048a, htr049a, htr4810a, htr489c])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
            linarith only [hlam, hc458yx, htr134c, htr148c, htr1810a, htr345a, htr4810a])
          obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd12a, hd910b, htr012a, htr014a, htr149a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc125xy, hc8910zy, htr012a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            linarith only [hlam, hc467zy, htr479c, htr4910a, htr679a, htr7910a]
          ·
            linarith only [hlam, hc127xy, hc689yz, htr012a, htr018a, htr179a, htr189a, htr6910a, htr7910a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd12a, hd45b, htr012a, htr014b, htr047a, htr345a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc456zy, htr346a, htr347a, htr467b, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr034c, htr048a, htr348a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr047c, htr048b, htr078c])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, htr047b, htr078a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc789yx, htr034c, htr047a, htr348a, htr478c, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc457yx, htr137c, htr179a, htr345a, htr347c, htr479a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hc7810yx, htr034c, htr047a, htr348a, htr4710a, htr478c])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
          linarith only [hlam, hc457yx, htr137c, htr1710a, htr345a, htr347c, htr4710a])
        obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr012a, htr014a, htr134c, htr348a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, hc478xy, htr047a, htr048b, htr089a, htr489a])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, htr478c, htr489a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd12a, hd910b, htr012a, htr017a, htr179a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr568a, htr568b, htr568c, _, _⟩
            linarith only [hlam, hc125xy, hc789zy, htr012a, htr017a, htr156a, htr179a, htr568a, htr689a])
          obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc126xy, hc679yz, htr012a, htr017a, htr168a, htr179a, htr568a, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          rcases m.htr 6 9 10 (by decide) (by decide) with
            ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          ·
            linarith only [hlam, hd67a, hd79b, htr567a, htr569a, htr6910a, htr7910a]
          ·
            linarith only [hlam, hc126xy, hc789zy, htr012a, htr017a, htr169a, htr179a, htr6910a, htr8910a]
        ·
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc126xy, hc7910zy, htr012a, htr017a, htr168a, htr1710a, htr689a, htr8910a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr568a, htr568b, htr568c, _, _⟩
            linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a])
          obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc126xy, hc468zy, htr012a, htr014a, htr134c, htr169a, htr348a, htr568a, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          rcases m.htr 6 9 10 (by decide) (by decide) with
            ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          ·
            linarith only [hlam, hc128xy, hc679yz, htr012a, htr017a, htr018c, htr089a, htr179a, htr6910a, htr8910a]
          ·
            linarith only [hlam, hc125xy, hc7910zy, htr012a, htr017a, htr156a, htr1710a, htr569a, htr6910a]
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc457yx, htr047a, htr048a, htr345a, htr348a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc456zy, htr346a, htr348a, htr468b, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        rcases m.htr 3 4 9 (by decide) (by decide) with
          ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, htr034c, htr049a, htr349a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr047c, htr049b, htr079c])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
            linarith only [hlam, htr048c, htr049b, htr089c])
          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc128xy, htr012a, htr018b, htr089a, htr189a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, htr047b, htr079a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc789xy, htr034c, htr047a, htr349a, htr478a, htr479c])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
          ·
            linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
        ·
          rcases m.htr 3 4 10 (by decide) (by decide) with
            ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
          ·
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, htr034c, htr0410a, htr3410a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0410b, htr047c, htr0710c])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
              linarith only [hlam, htr0410b, htr048c, htr0810c])
            obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
              linarith only [hlam, hc128xy, htr012a, htr018b, htr0810a, htr1810a])
            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, htr047b, htr0710a, htr4710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc7810xy, htr034c, htr047a, htr3410a, htr4710c, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            rcases m.htr 7 8 10 (by decide) (by decide) with
              ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd810b, htr012a, htr017a, htr178a, htr7810a]
            ·
              linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr1810a, htr7810a]
          ·
            rcases m.htr 3 7 8 (by decide) (by decide) with
              ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
            ·
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc125xy, hc789yx, htr012a, htr017a, htr137c, htr156a, htr378a, htr567a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr479a, htr679a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc457yx, htr137c, htr179a, htr345a, htr347c, htr479a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc125xy, hc789zy, htr012a, htr017a, htr156a, htr179a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hd45b, hd68a, htr345a, htr348a, htr489a, htr689a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc458yx, htr138c, htr189a, htr345a, htr348c, htr489a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr137c, htr378a, htr789a]
              ·
                linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc457yx, htr345a, htr347c, htr378a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc125xy, hc789xy, htr012a, htr017a, htr156a, htr179a, htr567a, htr678a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc457yx, htr137c, htr179a, htr345a, htr347c, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd45b, hd78a, htr345a, htr347a, htr479a, htr678a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc125xy, hc789yz, htr012a, htr018a, htr156a, htr189a, htr567a, htr679a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc458yx, htr138c, htr189a, htr345a, htr348c, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd45b, hd78a, htr345a, htr348a, htr489a, htr789a]
              ·
                linarith only [hlam, hd45b, hd89a, htr345a, htr347a, htr478a, htr789a]
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hd12a, hd45b, htr012a, htr014b, htr046a, htr345a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr034c, htr047a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr046c, htr047b, htr067c])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, htr046b, htr067a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc678yx, htr034c, htr046a, htr347a, htr467c, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc456yx, htr136c, htr168a, htr345a, htr346c, htr468a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc679yx, htr034c, htr046a, htr347a, htr467c, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc456yx, htr136c, htr169a, htr345a, htr346c, htr469a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
        linarith only [hlam, hc6710yx, htr034c, htr046a, htr347a, htr4610a, htr467c])
      obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
      have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
        linarith only [hlam, hc456yx, htr136c, htr1610a, htr345a, htr346c, htr4610a])
      obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr012a, htr014a, htr134c, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc467xy, htr046a, htr047b, htr078a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd12a, hd79b, htr012a, htr014a, htr134c, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, hc467xy, htr046a, htr047b, htr079a, htr479a])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, htr467c, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, htr467c, htr479a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12a, hd89b, htr012a, htr016a, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr012a, htr018a, htr189a, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd12a, hd910b, htr012a, htr016a, htr169a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc127xy, hc678zy, htr012a, htr016a, htr017c, htr079a, htr168a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc125xy, hc6910zy, htr012a, htr016a, htr157a, htr1610a, htr579a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc128xy, hc679zy, htr012a, htr016a, htr169a, htr189a, htr7910a, htr8910a]
      ·
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc125xy, hc689zy, htr012a, htr016a, htr157a, htr169a, htr578a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc127xy, hc679zy, htr012a, htr016a, htr017c, htr078a, htr169a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc127xy, hc689zy, htr012a, htr016a, htr017c, htr079a, htr169a, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc127xy, hc6910zy, htr012a, htr016a, htr017c, htr078a, htr1610a, htr789a, htr8910a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc456yx, htr046a, htr047a, htr345a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr034c, htr048a, htr348a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr046c, htr048b, htr068c])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr047c, htr048b, htr078c])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr046b, htr068a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc678xy, htr034c, htr046a, htr348a, htr467a, htr468c])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a]
        ·
          linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a]
      ·
        rcases m.htr 3 4 9 (by decide) (by decide) with
          ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, htr034c, htr049a, htr349a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr046c, htr049b, htr069c])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr047c, htr049b, htr079c])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hc127xy, htr012a, htr017b, htr079a, htr179a])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, htr046b, htr069a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc679xy, htr034c, htr046a, htr349a, htr467a, htr469c])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd79b, htr012a, htr016a, htr167a, htr679a]
          ·
            linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr179a, htr679a]
        ·
          rcases m.htr 3 4 10 (by decide) (by decide) with
            ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
          ·
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, htr034c, htr0410a, htr3410a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0410b, htr046c, htr0610c])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0410b, htr047c, htr0710c])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
              linarith only [hlam, hc127xy, htr012a, htr017b, htr0710a, htr1710a])
            obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, htr046b, htr0610a, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc6710xy, htr034c, htr046a, htr3410a, htr4610c, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd710b, htr012a, htr016a, htr167a, htr6710a]
            ·
              linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr1710a, htr6710a]
          ·
            rcases m.htr 3 6 7 (by decide) (by decide) with
              ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
            ·
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr136c, htr367a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd12a, hd79b, htr012a, htr016a, htr136c, htr367a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr179a, htr679a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc457yx, htr137c, htr179a, htr345a, htr347c, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd45b, hd89a, htr345a, htr347a, htr478a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hd45b, hd78a, htr345a, htr348a, htr489a, htr789a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc458yx, htr138c, htr189a, htr345a, htr348c, htr489a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd45b, hd910a, htr345a, htr347a, htr479a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hd45b, hd79a, htr345a, htr349a, htr4910a, htr7910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc459yx, htr139c, htr1910a, htr345a, htr349c, htr4910a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
              ·
                linarith only [hlam, hd12a, hd89b, htr012a, htr019a, htr1910a, htr8910a]
            ·
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc456yx, htr345a, htr346c, htr367a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd45b, hd78a, htr345a, htr346a, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd45b, hd79a, htr345a, htr346a, htr467a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr479a, htr679a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc457yx, htr137c, htr179a, htr345a, htr347c, htr479a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc458yx, htr138c, htr189a, htr345a, htr348c, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd12a, hd910b, htr012a, htr017a, htr179a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hd12a, hd79b, htr012a, htr019a, htr1910a, htr7910a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc459yx, htr139c, htr1910a, htr345a, htr349c, htr4910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd45b, hd89a, htr345a, htr349a, htr4910a, htr8910a]
              ·
                linarith only [hlam, hd45b, hd910a, htr345a, htr348a, htr489a, htr8910a]

theorem shard_360 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr139c : m.d 1 9 < m.d 3 9)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_360 m htr012a htr014a htr014b htr015a htr016a htr017a htr017b htr017c htr018a htr018b htr018c htr019a htr034c htr134c htr136c htr137c htr138c htr139c htr345a

#print axioms shard_360
end Jsp404.NoSatElevenDBMTerminal
