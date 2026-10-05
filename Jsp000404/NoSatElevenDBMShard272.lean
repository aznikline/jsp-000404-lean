import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_272 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr048b : m.d 4 8 < m.d 0 8)
    (htr049b : m.d 4 9 < m.d 0 9)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr147a : m.d 4 7 + lam ≤ m.d 1 4)
    (htr147b : m.d 4 7 < m.d 1 7)
    (htr147c : m.d 1 7 < m.d 1 4)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr148b : m.d 4 8 < m.d 1 8)
    (htr148c : m.d 1 8 < m.d 1 4)
    (htr149a : m.d 4 9 + lam ≤ m.d 1 4)
    (htr149b : m.d 4 9 < m.d 1 9)
    (htr157a : m.d 5 7 + lam ≤ m.d 1 5)
    (htr158a : m.d 5 8 + lam ≤ m.d 1 5)
    (htr159a : m.d 5 9 + lam ≤ m.d 1 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < 4*lam := by
    linarith only [hd14braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
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
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc057xy, hc057yx, hc057yz, hc057zy⟩ := endpoint_caps m 0 5 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc124zy, htr145c, htr157a, htr245a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc124zy, htr145c, htr158a, htr245a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc124zy, htr145c, htr159a, htr245a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd14b, hd67a, htr145a, htr245a, htr246a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hd12b, hd46a, htr012a, htr016a, htr167a, htr467a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc126yx, htr012a, htr016c, htr067a, htr167a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hd14b, hd68a, htr145a, htr245a, htr246a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hd12b, hd46a, htr012a, htr016a, htr168a, htr468a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hd14b, hd69a, htr145a, htr245a, htr246a, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, hd12b, hd46a, htr012a, htr016a, htr169a, htr469a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, hc126yx, htr012a, htr016c, htr069a, htr169a])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  rcases m.htr 2 4 7 (by decide) (by decide) with
    ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
  ·
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc124zy, htr014a, htr017a, htr147b, htr247a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc346zy, htr246a, htr247a, htr367a, htr467c])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    rcases m.htr 2 4 8 (by decide) (by decide) with
      ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
    ·
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc124zy, htr014a, htr018a, htr148b, htr248a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      rcases m.htr 2 4 9 (by decide) (by decide) with
        ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
      ·
        have hforced019 := (m.htr 0 1 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr019a, htr019b, htr019c, _, _⟩
          linarith only [hlam, hc124zy, htr014a, htr019a, htr149b, htr249a])
        obtain ⟨htr019a, htr019b, htr019c, _, _⟩ := hforced019
        rcases m.htr 2 4 10 (by decide) (by decide) with
          ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
        ·
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc124zy, htr147c, htr178a, htr247a, htr478a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, htr247c, htr278a, htr478a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hd46a, hd89b, htr246a, htr247a, htr478a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hd46a, hd78b, htr246a, htr248a, htr489a, htr789a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc134xy, hc578yz, htr013a, htr017a, htr148a, htr178a, htr489a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc134xy, hc789zy, htr013a, htr017a, htr145a, htr179a, htr458a, htr589a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
              linarith only [hlam, hc134xy, hc8910xy, htr013a, htr018a, htr145a, htr1810a, htr458a, htr589a])
            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
              linarith only [hlam, hd46a, hd78b, htr178a, htr179a, htr246a, htr247b, htr279a])
            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
            have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
              linarith only [hlam, hc138xy, hc789yx, htr013a, htr017a, htr178a, htr1810a, htr278b, htr279a, htr2810a])
            obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
            have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
              linarith only [hlam, hc123yx, hc578yz, htr013a, htr017a, htr128a, htr178a, htr2810a, htr5810a])
            obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
              linarith only [hlam, hc134xy, hc8910yz, htr013a, htr019a, htr145a, htr1910a, htr458a, htr5810a])
            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hc789yx, htr178a, htr179c, htr1910a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hd78b, hd89a, htr178a, htr179a, htr7910a, htr8910a]
            ·
              linarith only [hlam, hd14b, hd910a, htr145a, htr458a, htr589a, htr8910a]
          ·
            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
              linarith only [hlam, htr047b, htr078a, htr478a])
            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, htr147b, htr178a, htr478a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hc124zy, htr147a, htr247b, htr278a, htr478a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd14b, hd79a, htr147a, htr478a, htr578a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              rcases m.htr 6 7 9 (by decide) (by decide) with
                ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
              ·
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, htr067c, htr079a, htr679a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, htr078c, htr079b, htr089c])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hd46a, hd79b, htr048b, htr089a, htr167c, htr178c, htr189a, htr246a, htr248a, htr679a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, htr127b, htr167c, htr279a, htr679a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  linarith only [hlam, hc134xy, hc8910yx, htr013a, htr018a, htr147a, htr189a, htr478a, htr7810a])
                obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, hc057zy, htr078c, htr0810a, htr578a, htr7810a])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hd46a, hd79b, htr048b, htr0810a, htr167c, htr178c, htr1810a, htr246a, htr248a, htr679a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                  linarith only [hlam, hc134xy, hc8910zy, htr013a, htr018a, htr145a, htr1810a, htr459a, htr5910a])
                obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                  linarith only [hlam, hc123yx, hc579yz, htr013a, htr017a, htr129a, htr167c, htr2910a, htr5910a, htr679a])
                obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd46a, hd910b, htr048b, htr089a, htr246a, htr248a, htr8910a]
                ·
                  linarith only [hlam, hd57a, hd89b, htr278a, htr279b, htr2910a, htr578a, htr8910a]
              ·
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hc567yz, htr047b, htr079a, htr478a, htr578a, htr679a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, hc567yz, htr278a, htr279a, htr578a, htr679a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                rcases m.htr 6 7 10 (by decide) (by decide) with
                  ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                ·
                  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                    linarith only [hlam, htr067c, htr0710a, htr6710a])
                  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                    linarith only [hlam, htr0710b, htr078c, htr0810c])
                  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                    linarith only [hlam, htr0710b, htr079c, htr0910c])
                  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                  have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                    linarith only [hlam, hd46a, hd710b, htr048b, htr0810a, htr167c, htr178c, htr1810a, htr246a, htr248a, htr6710a])
                  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hc134xy, hc8910xy, htr013a, htr018a, htr147a, htr1810a, htr478a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, hc057zy, htr078c, htr089a, htr578a, htr789a])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd46a, hd910b, htr048b, htr089a, htr246a, htr248a, htr8910a]
                  ·
                    linarith only [hlam, hd46a, hd89b, htr049b, htr0910a, htr246a, htr249a, htr8910a]
                ·
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, hc057zy, htr078c, htr089a, htr578a, htr789a])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc157zy, htr178c, htr189a, htr578a, htr789a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      linarith only [hlam, hc134xy, hc8910yx, htr013a, htr018a, htr147a, htr189a, htr478a, htr7810a])
                    obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc057zy, htr078c, htr0810a, htr578a, htr7810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hd46a, hd89b, htr048b, htr0810a, htr1810a, htr189a, htr246a, htr248a])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                      linarith only [hlam, hc134xy, hc8910zy, htr013a, htr018a, htr145a, htr1810a, htr459a, htr5910a])
                    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                    have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                      linarith only [hlam, hc123yx, hc589yz, htr013a, htr018a, htr129a, htr189a, htr2910a, htr5910a])
                    obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                    have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                      linarith only [hlam, hc567yz, htr069c, htr0910a, htr279b, htr2910a, htr579a, htr679c])
                    obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd46a, hd910b, htr048b, htr089a, htr246a, htr248a, htr8910a]
                    ·
                      linarith only [hlam, hd46a, hd89b, htr049b, htr0910a, htr246a, htr249a, htr8910a]
                  ·
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hc134xy, hc8910xy, htr013a, htr018a, htr147a, htr1810a, htr478a, htr789a])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                      linarith only [hlam, hc157zy, htr178c, htr1810a, htr278b, htr2810a, htr578a])
                    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hd14b, hd58a, htr147a, htr478a, htr589a, htr789a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                      linarith only [hlam, hd12b, hd89a, htr128a, htr2810a, htr5810a, htr589a])
                    obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                    have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                      linarith only [hlam, hc134xy, hc8910yz, htr013a, htr019a, htr145a, htr1910a, htr458a, htr5810a])
                    obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hc567yz, htr169c, htr1910a, htr579a, htr679c, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd12b, hd89a, htr127a, htr279a, htr7910a, htr8910a]
                    ·
                      linarith only [hlam, hd14b, hd910a, htr147a, htr478a, htr789a, htr8910a]
            ·
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc134xy, hc789xy, htr013a, htr017a, htr145a, htr179a, htr457a, htr578a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hc134xy, hc7810xy, htr013a, htr017a, htr145a, htr1710a, htr457a, htr578a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc124zy, htr147c, htr179a, htr247a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                linarith only [hlam, hc124zy, htr147c, htr1710a, htr247a, htr4710a])
              obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd14b, hd78a, htr147a, htr479a, htr578a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc134xy, hc789yz, htr013a, htr018a, htr145a, htr189a, htr457a, htr579a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc124zy, htr148c, htr189a, htr248a, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                linarith only [hlam, hd14b, hd78a, htr147a, htr4710a, htr5710a, htr578a])
              obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc134xy, hc7910yz, htr013a, htr019a, htr145a, htr1910a, htr457a, htr5710a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd14b, hd89a, htr145a, htr457a, htr578a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd14b, hd910a, htr145a, htr457a, htr579a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc178zy, htr189c, htr1910a, htr789a, htr8910a]
              ·
                linarith only [hlam, hd14b, hd79a, htr148a, htr489a, htr7910a, htr8910a]
        ·
          have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
            linarith only [hlam, htr2410c, htr247b, htr2710b])
          obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
          have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
            linarith only [hlam, htr2410c, htr248b, htr2810b])
          obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, htr247c, htr2710a, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc7810yx, htr2410a, htr247a, htr4710b, htr478a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, htr248c, htr2810a, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hd14b, hd57a, htr145a, htr2410a, htr245a, htr4710b, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd14b, hd710a, htr147a, htr478a, htr5710a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd14b, hd78a, htr145a, htr2410a, htr245a, htr4810b, htr7810a]
          ·
            linarith only [hlam, hd14b, hd810a, htr145a, htr457a, htr578a, htr7810a]
      ·
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, htr247b, htr249c, htr279b])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, htr248b, htr249c, htr289b])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, htr247c, htr279a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc789yx, htr247a, htr249a, htr478a, htr479b])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, htr248c, htr289a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd14b, hd57a, htr145a, htr245a, htr249a, htr479b, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd14b, hd79a, htr147a, htr478a, htr578a, htr579a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd14b, hd78a, htr145a, htr245a, htr249a, htr489b, htr789a]
        ·
          linarith only [hlam, hd14b, hd89a, htr145a, htr457a, htr578a, htr789a]
    ·
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
        linarith only [hlam, hc789xy, htr247a, htr248a, htr478b, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hc7810xy, htr247a, htr248a, htr4710a, htr478b])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd14b, hd89a, htr145a, htr245a, htr248a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd14b, hd57a, htr145a, htr245a, htr248a, htr478b, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd14b, hd78a, htr147a, htr479a, htr578a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hd14b, hd78a, htr147a, htr4710a, htr5710a, htr578a])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, htr478b, htr489a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd14b, hd910a, htr145a, htr457a, htr579a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc134xy, hc789yz, htr136a, htr145a, htr368a, htr457a, htr579a, htr689a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc146yx, hc679zy, htr145a, htr168a, htr368a, htr369a, htr457a, htr579a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd67b, hd79a, htr367a, htr369a, htr6910a, htr7910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc146yx, hc7910yz, htr145a, htr168a, htr457a, htr5710a, htr689a, htr8910a]
        ·
          linarith only [hlam, hc146yx, hc789yz, htr145a, htr169a, htr457a, htr579a, htr6910a, htr8910a]
      ·
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc346zy, htr368a, htr468b, htr489a, htr689a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc146yx, hc468yz, htr145a, htr169a, htr245a, htr248a, htr368a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc134xy, hc7910yz, htr136a, htr145a, htr369a, htr457a, htr5710a, htr6910a])
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
      linarith only [hlam, hd14b, hd78a, htr145a, htr245a, htr247a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd14b, hd79a, htr145a, htr245a, htr247a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    rcases m.htr 3 6 7 (by decide) (by decide) with
      ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
    ·
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc146yx, hc467yz, htr145a, htr168a, htr245a, htr247a, htr367a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hc146yx, hc467yz, htr145a, htr169a, htr245a, htr247a, htr367a, htr369a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc134xy, hc478yz, htr136a, htr145a, htr245a, htr248a, htr367a, htr678a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc124zy, htr014a, htr018a, htr148b, htr248a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr136a, htr367a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd46a, hd78b, htr246a, htr248a, htr489a, htr789a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc134xy, hc578yz, htr136a, htr148a, htr367a, htr489a, htr589a, htr678a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc134xy, hc8910xy, htr013a, htr018a, htr145a, htr1810a, htr458a, htr589a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hc124zy, htr148c, htr1810a, htr248a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc134xy, hc578yz, htr136a, htr148a, htr367a, htr4810a, htr5810a, htr678a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc134xy, hc789zy, htr136a, htr145a, htr367a, htr458a, htr589a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr249a, htr249b, htr249c, _, _⟩
          linarith only [hlam, hc467yz, htr247a, htr249a, htr479c, htr679a])
        obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd14b, hd910a, htr145a, htr245a, htr249a, htr4910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc134xy, hc8910yz, htr136a, htr145a, htr369a, htr458a, htr5810a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a]
        ·
          linarith only [hlam, hc467yz, htr479b, htr4910a, htr679a, htr7910a]
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc467yz, htr247a, htr248a, htr478c, htr678a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd14b, hd89a, htr145a, htr245a, htr248a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hd14b, hd810a, htr145a, htr245a, htr248a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr249a, htr249b, htr249c, _, _⟩
          linarith only [hlam, hc134xy, hc489yz, htr136a, htr145a, htr245a, htr249a, htr368a, htr689a])
        obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc467yz, htr478b, htr4810a, htr678a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc467yz, htr478a, htr678c, htr6810a, htr7810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc134xy, hc8910zy, htr136a, htr145a, htr368a, htr459a, htr5910a, htr6810a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc134xy, hc589yz, htr136a, htr149a, htr368a, htr4910a, htr5910a, htr689a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd13a, hd910b, htr136a, htr368a, htr689a, htr8910a]
        ·
          linarith only [hlam, hd46a, hd89b, htr246a, htr249a, htr4910a, htr8910a]
    ·
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc346zy, htr367a, htr467b, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc346zy, htr367a, htr467b, htr479a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      rcases m.htr 3 6 8 (by decide) (by decide) with
        ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc146yx, hc468yz, htr145a, htr167a, htr245a, htr248a, htr367a, htr368a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc124zy, htr014a, htr018a, htr148b, htr248a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd46a, hd89b, htr367a, htr368a, htr467a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd46a, hd68b, htr246a, htr248a, htr489a, htr689a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc146yx, hc568yz, htr148a, htr167a, htr367a, htr368a, htr489a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc134xy, hc8910xy, htr013a, htr018a, htr145a, htr1810a, htr458a, htr589a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc146yx, hc689zy, htr145a, htr167a, htr367a, htr369a, htr458a, htr589a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr249a, htr249b, htr249c, _, _⟩
          linarith only [hlam, hc346zy, htr246a, htr249a, htr369a, htr469c])
        obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hc124zy, htr148c, htr1810a, htr248a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd14b, hd910a, htr145a, htr245a, htr249a, htr4910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc146yx, hc568yz, htr148a, htr167a, htr367a, htr368a, htr4810a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc346zy, htr369a, htr469b, htr4910a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc146yx, hc8910yz, htr145a, htr167a, htr458a, htr5810a, htr679a, htr7910a]
        ·
          linarith only [hlam, hc146yx, hc789zy, htr145a, htr169a, htr458a, htr589a, htr6910a, htr7910a]
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc346zy, htr246a, htr248a, htr368a, htr468c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd14b, hd89a, htr145a, htr245a, htr248a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hd14b, hd810a, htr145a, htr245a, htr248a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc346zy, htr368a, htr468b, htr489a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc346zy, htr368a, htr468b, htr4810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc146yx, hc478yz, htr145a, htr168a, htr245a, htr248a, htr689a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr249a, htr249b, htr249c, _, _⟩
          linarith only [hlam, hc146yx, hc489yz, htr145a, htr167a, htr245a, htr249a, htr678a, htr789a])
        obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc346zy, htr246a, htr249a, htr369a, htr469c])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd46a, hd910b, htr367a, htr369a, htr467a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd46a, hd69b, htr246a, htr249a, htr4910a, htr6910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc146yx, hc589yz, htr149a, htr167a, htr4910a, htr5910a, htr678a, htr789a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc146yx, hc8910zy, htr145a, htr167a, htr459a, htr5910a, htr678a, htr7810a]
        ·
          linarith only [hlam, hc146yx, hc478yz, htr145a, htr168a, htr245a, htr248a, htr6810a, htr7810a]

theorem shard_272 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr048b : m.d 4 8 < m.d 0 8)
    (htr049b : m.d 4 9 < m.d 0 9)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr147a : m.d 4 7 + lam ≤ m.d 1 4)
    (htr147b : m.d 4 7 < m.d 1 7)
    (htr147c : m.d 1 7 < m.d 1 4)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr148b : m.d 4 8 < m.d 1 8)
    (htr148c : m.d 1 8 < m.d 1 4)
    (htr149a : m.d 4 9 + lam ≤ m.d 1 4)
    (htr149b : m.d 4 9 < m.d 1 9)
    (htr157a : m.d 5 7 + lam ≤ m.d 1 5)
    (htr158a : m.d 5 8 + lam ≤ m.d 1 5)
    (htr159a : m.d 5 9 + lam ≤ m.d 1 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    : False :=
  proof_shard_272 m htr012a htr013a htr014a htr016a htr016c htr047b htr048b htr049b htr127a htr127b htr128a htr129a htr136a htr145a htr145c htr147a htr147b htr147c htr148a htr148b htr148c htr149a htr149b htr157a htr158a htr159a htr245a htr246a

#print axioms shard_272
end Jsp404.NoSatElevenDBMTerminal
