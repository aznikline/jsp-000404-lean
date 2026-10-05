import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_022 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd510a := (m.hrange 5 10 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
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
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc469xy, hc469yx, hc469yz, hc469zy⟩ := endpoint_caps m 4 6 9 (by decide) (by decide)
  obtain ⟨hc4610xy, hc4610yx, hc4610yz, hc4610zy⟩ := endpoint_caps m 4 6 10 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  rcases m.htr 0 3 7 (by decide) (by decide) with
    ⟨htr037a, htr037b, htr037c, _, _⟩ | ⟨htr037a, htr037b, htr037c, _, _⟩
  ·
    rcases m.htr 3 4 8 (by decide) (by decide) with
      ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
    ·
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr034c, htr048a, htr348a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr045c, htr048b, htr058c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr046c, htr048b, htr068c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, hc023yz, htr034a, htr124c, htr148a, htr234c, htr348a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc468xy, htr046b, htr068a, htr146c, htr148a, htr168a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc023yz, htr034a, htr234c, htr248a, htr348a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc023yz, htr036a, htr136b, htr168a, htr236c, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, htr045b, htr058a, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc568xy, htr034c, htr045a, htr348a, htr456a, htr458c])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc458xy, htr245c, htr248a, htr256a, htr456a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        linarith only [hlam, hd01a, hd68b, htr012a, htr125a, htr256a, htr568a]
      ·
        linarith only [hlam, hd01a, hd56b, htr012a, htr126a, htr268a, htr568a]
    ·
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr134a, htr138a, htr348c])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, htr123c, htr134a, htr238a, htr348c])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      rcases m.htr 0 3 8 (by decide) (by decide) with
        ⟨htr038a, htr038b, htr038c, _, _⟩ | ⟨htr038a, htr038b, htr038c, _, _⟩
      ·
        rcases m.htr 3 4 9 (by decide) (by decide) with
          ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, htr034c, htr049a, htr349a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr045c, htr049b, htr059c])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr046c, htr049b, htr069c])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr149a, htr149b, htr149c, _, _⟩
            linarith only [hlam, hc023yz, htr034a, htr124c, htr149a, htr234c, htr349a])
          obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hc469xy, htr046b, htr069a, htr146c, htr149a, htr169a])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr249a, htr249b, htr249c, _, _⟩
            linarith only [hlam, hc023yz, htr034a, htr234c, htr249a, htr349a])
          obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
          have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr269a, htr269b, htr269c, _, _⟩
            linarith only [hlam, hc023yz, htr036a, htr136b, htr169a, htr236c, htr269a])
          obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, htr045b, htr059a, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr456a, htr456b, htr456c, _, _⟩
            linarith only [hlam, hc569xy, htr034c, htr045a, htr349a, htr456a, htr459c])
          obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc459xy, htr245c, htr249a, htr256a, htr456a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            linarith only [hlam, hd01a, hd69b, htr012a, htr125a, htr256a, htr569a]
          ·
            linarith only [hlam, hd01a, hd56b, htr012a, htr126a, htr269a, htr569a]
        ·
          have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr139a, htr139b, htr139c, _, _⟩
            linarith only [hlam, htr134a, htr139a, htr349c])
          obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
          rcases m.htr 0 3 9 (by decide) (by decide) with
            ⟨htr039a, htr039b, htr039c, _, _⟩ | ⟨htr039a, htr039b, htr039c, _, _⟩
          ·
            rcases m.htr 3 4 10 (by decide) (by decide) with
              ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
            ·
              have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                linarith only [hlam, htr034c, htr0410a, htr3410a])
              obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
              have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                linarith only [hlam, htr0410b, htr045c, htr0510c])
              obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                linarith only [hlam, htr0410b, htr046c, htr0610c])
              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
              have hforced1410 := (m.htr 1 4 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1410a, htr1410b, htr1410c, _, _⟩
                linarith only [hlam, hc023yz, htr034a, htr124c, htr1410a, htr234c, htr3410a])
              obtain ⟨htr1410a, htr1410b, htr1410c, _, _⟩ := hforced1410
              have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                linarith only [hlam, hc4610xy, htr046b, htr0610a, htr1410a, htr146c, htr1610a])
              obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
              have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
                linarith only [hlam, hc023yz, htr034a, htr234c, htr2410a, htr3410a])
              obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
              have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                linarith only [hlam, hc023yz, htr036a, htr136b, htr1610a, htr236c, htr2610a])
              obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
              have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                linarith only [hlam, htr045b, htr0510a, htr4510a])
              obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
              have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr456a, htr456b, htr456c, _, _⟩
                linarith only [hlam, hc5610xy, htr034c, htr045a, htr3410a, htr4510c, htr456a])
              obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hc4510xy, htr2410a, htr245c, htr256a, htr456a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                linarith only [hlam, hd01a, hd610b, htr012a, htr125a, htr256a, htr5610a]
              ·
                linarith only [hlam, hd01a, hd56b, htr012a, htr126a, htr2610a, htr5610a]
            ·
              rcases m.htr 0 3 10 (by decide) (by decide) with
                ⟨htr0310a, htr0310b, htr0310c, _, _⟩ | ⟨htr0310a, htr0310b, htr0310c, _, _⟩
              ·
                rcases m.htr 4 5 6 (by decide) (by decide) with
                  ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
                ·
                  rcases m.htr 2 5 6 (by decide) (by decide) with
                    ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
                  ·
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hd01a, hd67b, htr012a, htr125a, htr256a, htr567a])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                      linarith only [hlam, hd01a, hd56b, htr012a, htr126a, htr267a, htr567a])
                    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                      linarith only [hlam, hc023yz, htr036a, htr236c, htr267a, htr367a])
                    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hd01a, hd68b, htr012a, htr125a, htr256a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hd01a, hd56b, htr012a, htr126a, htr268a, htr568a])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                      linarith only [hlam, hc023yz, htr036a, htr236c, htr268a, htr368a])
                    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hd01a, hd69b, htr012a, htr125a, htr256a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                      linarith only [hlam, hd01a, hd56b, htr012a, htr126a, htr269a, htr569a])
                    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                      linarith only [hlam, hc023yz, htr036a, htr236c, htr269a, htr369a])
                    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                      linarith only [hlam, hd01a, hd610b, htr012a, htr125a, htr256a, htr5610a])
                    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                    have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                      linarith only [hlam, hd01a, hd56b, htr012a, htr126a, htr2610a, htr5610a])
                    obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
                    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
                      linarith only [hlam, hc023yz, htr036a, htr236c, htr2610a, htr3610a])
                    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
                    rcases m.htr 4 6 7 (by decide) (by decide) with
                      ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                    ·
                      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                        linarith only [hlam, hc456yz, htr125c, htr157a, htr256a, htr467a, htr567b])
                      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                        linarith only [hlam, hc023yz, hc456yz, htr035a, htr135b, htr157a, htr234a, htr256a, htr257a, htr346c, htr367a, htr467a])
                      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                        linarith only [hlam, hd23b, hd68a, htr234a, htr346c, htr367a, htr467a, htr468a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                        linarith only [hlam, hc456yz, htr125c, htr158a, htr256a, htr468a, htr568b])
                      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                        linarith only [hlam, hc023yz, hc456yz, htr035a, htr135b, htr158a, htr234a, htr256a, htr258a, htr346c, htr367a, htr467a])
                      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hd01a, hd78b, htr012a, htr125a, htr257a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hd01a, hd89b, htr012a, htr125a, htr258a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hc456yz, htr468a, htr568c, htr589a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd23b, hd78a, htr234a, htr346c, htr368a, htr689a, htr789a]
                      ·
                        linarith only [hlam, hd23b, hd89a, htr234a, htr346c, htr367a, htr678a, htr789a]
                    ·
                      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                        linarith only [hlam, hd23b, hd67a, htr234a, htr346c, htr368a, htr467a, htr468a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                        linarith only [hlam, hd23b, hd67a, htr234a, htr346c, htr369a, htr467a, htr469a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                        linarith only [hlam, hd23b, hd67a, htr234a, htr346c, htr3610a, htr4610a, htr467a])
                      obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hd23b, hd78a, htr234a, htr346a, htr467a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                        linarith only [hlam, hd23b, hd79a, htr234a, htr346a, htr467a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd23b, hd89a, htr234a, htr346a, htr468a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                        linarith only [hlam, hd23b, hd910a, htr234a, htr346a, htr469a, htr6910a])
                      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                      rcases m.htr 3 5 7 (by decide) (by decide) with
                        ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                      ·
                        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                          linarith only [hlam, hc023yz, htr035a, htr125c, htr157a, htr235c, htr357a])
                        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc023yz, hc678yz, htr035a, htr234a, htr346a, htr357a, htr468a, htr578a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                          linarith only [hlam, hc567zy, htr157a, htr158a, htr578b, htr678a])
                        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc023yz, hc689yz, htr035a, htr135b, htr158a, htr234a, htr346a, htr469a, htr589a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a]
                        ·
                          linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a]
                      ·
                        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                          linarith only [hlam, htr135b, htr157a, htr357a])
                        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hd23b, hd67a, htr235a, htr357a, htr578a, htr678a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                          linarith only [hlam, hc567yx, htr125c, htr157c, htr178a, htr256a, htr578a])
                        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hd23b, hd67a, htr235a, htr357a, htr579a, htr679a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc567yx, htr125c, htr157c, htr179a, htr256a, htr579a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                          linarith only [hlam, hc023yz, hc689yz, htr037a, htr137b, htr178a, htr234a, htr346a, htr469a, htr789a])
                        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hc023yz, hc6910yz, htr037a, htr137b, htr179a, htr234a, htr346a, htr4610a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
                        ·
                          linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
                  ·
                    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                      linarith only [hlam, hc023yz, htr035a, htr235c, htr256a, htr356a])
                    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
                    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                      linarith only [hlam, hc023yz, htr035b, htr056a, htr235a, htr356a])
                    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                      linarith only [hlam, hd23b, hd57a, htr235a, htr356a, htr456a, htr457a])
                    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                      linarith only [hlam, hd23b, hd58a, htr235a, htr356a, htr456a, htr458a])
                    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
                    have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr459a, htr459b, htr459c, _, _⟩
                      linarith only [hlam, hd23b, hd59a, htr235a, htr356a, htr456a, htr459a])
                    obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
                    rcases m.htr 3 5 7 (by decide) (by decide) with
                      ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                    ·
                      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                        linarith only [hlam, htr035c, htr057a, htr357a])
                      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                        linarith only [hlam, htr056c, htr057b, htr067c])
                      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, htr056b, htr067a, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                        linarith only [hlam, hc678yx, htr035c, htr056a, htr357a, htr567c, htr568a])
                      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                        linarith only [hlam, hc245zy, htr256c, htr268a, htr456a, htr568a])
                      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, hc679yx, htr035c, htr056a, htr357a, htr567c, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                        linarith only [hlam, hc245zy, htr256c, htr269a, htr456a, htr569a])
                      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hd45a, hd78b, htr356a, htr357a, htr456a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, hc567xy, htr056a, htr057b, htr078a, htr578a])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hd45a, hd79b, htr356a, htr357a, htr456a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, hc567xy, htr056a, htr057b, htr079a, htr579a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, htr567c, htr578a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                        linarith only [hlam, htr567c, htr579a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd01a, hd89b, htr012a, htr126a, htr268a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                        linarith only [hlam, hd01a, hd68b, htr012a, htr128a, htr289a, htr689a])
                      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc023yz, htr038a, htr238c, htr289a, htr389a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                        linarith only [hlam, hd01a, hd910b, htr012a, htr126a, htr269a, htr6910a])
                      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hd23b, hd78a, htr034c, htr047c, htr079a, htr234a, htr478a, htr479a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hd23b, hd910a, htr234a, htr347a, htr479a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
                        ·
                          linarith only [hlam, hd23b, hd79a, htr234a, htr348c, htr389a, htr7910a, htr8910a]
                      ·
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hd23b, hd89a, htr234a, htr347a, htr478a, htr789a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hd23b, hd79a, htr034c, htr047c, htr078a, htr234a, htr478a, htr479a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd23b, hd89a, htr034c, htr047c, htr079a, htr234a, htr7910a, htr8910a]
                        ·
                          linarith only [hlam, hd23b, hd910a, htr034c, htr047c, htr078a, htr234a, htr789a, htr8910a]
                    ·
                      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                        linarith only [hlam, hc345zy, htr056a, htr057a, htr357a, htr456a])
                      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                        linarith only [hlam, htr235b, htr257a, htr357a])
                      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                      rcases m.htr 3 5 8 (by decide) (by decide) with
                        ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
                      ·
                        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                          linarith only [hlam, htr035c, htr058a, htr358a])
                        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                          linarith only [hlam, htr056c, htr058b, htr068c])
                        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                          linarith only [hlam, htr057c, htr058b, htr078c])
                        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                          linarith only [hlam, hc245zy, htr057b, htr078a, htr257c, htr278a, htr457a])
                        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                          linarith only [hlam, htr056b, htr068a, htr568a])
                        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc678xy, htr035c, htr056a, htr358a, htr567a, htr568c])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                          linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a])
                        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                        rcases m.htr 6 7 8 (by decide) (by decide) with
                          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                        ·
                          linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a]
                        ·
                          linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr278a, htr678a]
                      ·
                        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                          linarith only [hlam, htr135b, htr158a, htr358a])
                        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                          linarith only [hlam, htr235b, htr258a, htr358a])
                        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                        rcases m.htr 3 5 9 (by decide) (by decide) with
                          ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
                        ·
                          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                            linarith only [hlam, htr035c, htr059a, htr359a])
                          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                            linarith only [hlam, htr056c, htr059b, htr069c])
                          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                            linarith only [hlam, htr057c, htr059b, htr079c])
                          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                            linarith only [hlam, hc245zy, htr057b, htr079a, htr257c, htr279a, htr457a])
                          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                            linarith only [hlam, htr056b, htr069a, htr569a])
                          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                            linarith only [hlam, hc679xy, htr035c, htr056a, htr359a, htr567a, htr569c])
                          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                            linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a])
                          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                          rcases m.htr 6 7 9 (by decide) (by decide) with
                            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                          ·
                            linarith only [hlam, hd01a, hd79b, htr012a, htr126a, htr267a, htr679a]
                          ·
                            linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr279a, htr679a]
                        ·
                          have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr159a, htr159b, htr159c, _, _⟩
                            linarith only [hlam, htr135b, htr159a, htr359a])
                          obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
                          rcases m.htr 3 5 10 (by decide) (by decide) with
                            ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                          ·
                            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                              linarith only [hlam, htr035c, htr0510a, htr3510a])
                            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                              linarith only [hlam, htr0510b, htr056c, htr0610c])
                            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                              linarith only [hlam, htr0510b, htr057c, htr0710c])
                            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                              linarith only [hlam, hc245zy, htr057b, htr0710a, htr257c, htr2710a, htr457a])
                            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                              linarith only [hlam, htr056b, htr0610a, htr5610a])
                            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                              linarith only [hlam, hc6710xy, htr035c, htr056a, htr3510a, htr5610c, htr567a])
                            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                              linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a])
                            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                            rcases m.htr 6 7 10 (by decide) (by decide) with
                              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                            ·
                              linarith only [hlam, hd01a, hd710b, htr012a, htr126a, htr267a, htr6710a]
                            ·
                              linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr2710a, htr6710a]
                          ·
                            rcases m.htr 5 6 7 (by decide) (by decide) with
                              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                            ·
                              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                                linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a])
                              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                                linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a])
                              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                                linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr278a, htr678a])
                              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                                linarith only [hlam, hc245zy, htr257c, htr278a, htr457a, htr578a])
                              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                                linarith only [hlam, hd23b, hd47a, htr235a, htr357a, htr478a, htr578a])
                              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                                linarith only [hlam, hd01a, hd79b, htr012a, htr126a, htr267a, htr679a])
                              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                                linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr279a, htr679a])
                              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                                linarith only [hlam, hc245zy, htr057b, htr079a, htr257c, htr279a, htr457a])
                              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                                linarith only [hlam, hd23b, hd78a, htr034c, htr047c, htr079a, htr234a, htr478a, htr479a])
                              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                              have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                                linarith only [hlam, hd01a, hd710b, htr012a, htr126a, htr267a, htr6710a])
                              obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                              have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                                linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr2710a, htr6710a])
                              obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                                linarith only [hlam, hc245zy, htr057b, htr0710a, htr257c, htr2710a, htr457a])
                              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                              have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                                linarith only [hlam, hd23b, hd78a, htr034c, htr047c, htr0710a, htr234a, htr4710a, htr478a])
                              obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                                linarith only [hlam, hd23b, hd89a, htr235a, htr357a, htr578a, htr789a])
                              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                                linarith only [hlam, hd23b, hd78a, htr235a, htr358a, htr589a, htr789a])
                              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                                linarith only [hlam, hc145zy, htr158c, htr189a, htr458a, htr589a])
                              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                                linarith only [hlam, hd23b, hd910a, htr234a, htr347a, htr479a, htr7910a])
                              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                              have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                                linarith only [hlam, hd23b, hd79a, htr235a, htr359a, htr5910a, htr7910a])
                              obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                                linarith only [hlam, hc145zy, htr159c, htr1910a, htr459a, htr5910a])
                              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                              rcases m.htr 8 9 10 (by decide) (by decide) with
                                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                              ·
                                linarith only [hlam, hc023yz, hc7910yz, htr038a, htr138b, htr189a, htr234a, htr347a, htr4710a, htr8910a]
                              ·
                                linarith only [hlam, hc023yz, hc789yz, htr039a, htr139b, htr1910a, htr234a, htr347a, htr479a, htr8910a]
                            ·
                              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                                linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a])
                              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                                linarith only [hlam, hd23b, hd67a, htr235a, htr357a, htr578a, htr678a])
                              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                                linarith only [hlam, hc245zy, htr257c, htr278a, htr457a, htr578a])
                              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                                linarith only [hlam, hd23b, hd79a, htr235a, htr356a, htr567a, htr679a])
                              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                                linarith only [hlam, hd23b, hd67a, htr235a, htr357a, htr579a, htr679a])
                              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                                linarith only [hlam, hc245zy, htr257c, htr279a, htr457a, htr579a])
                              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                                linarith only [hlam, hd01a, hd89b, htr012a, htr127a, htr278a, htr789a])
                              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                                linarith only [hlam, hd01a, hd78b, htr012a, htr128a, htr289a, htr789a])
                              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                                linarith only [hlam, hc245zy, htr258c, htr289a, htr458a, htr589a])
                              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                                linarith only [hlam, hd01a, hd910b, htr012a, htr127a, htr279a, htr7910a])
                              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                                linarith only [hlam, hc023yz, hc789zy, htr039a, htr139b, htr1910a, htr235a, htr358a, htr589a, htr7910a])
                              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                              have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                                linarith only [hlam, hc145zy, htr159c, htr1910a, htr459a, htr5910a])
                              obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                              rcases m.htr 8 9 10 (by decide) (by decide) with
                                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                              ·
                                linarith only [hlam, hd23b, hd89a, htr235a, htr359a, htr5910a, htr8910a]
                              ·
                                linarith only [hlam, hd23b, hd910a, htr235a, htr358a, htr589a, htr8910a]
                ·
                  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                    linarith only [hlam, htr045b, htr056a, htr456a])
                  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                    linarith only [hlam, htr135b, htr156a, htr345b, htr456a])
                  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
                  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                    linarith only [hlam, htr245b, htr256a, htr456a])
                  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, hd23b, hd67a, htr234a, htr345a, htr456a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hd23b, hd68a, htr234a, htr345a, htr456a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hd23b, hd56a, htr234a, htr346a, htr468a, htr568a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  rcases m.htr 4 5 7 (by decide) (by decide) with
                    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hd23b, hd56a, htr034c, htr045c, htr057a, htr234a, htr456a, htr457a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                      linarith only [hlam, hd23b, hd56a, htr235a, htr357a, htr456a, htr457a])
                    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                      linarith only [hlam, hc023yz, htr035a, htr125c, htr157a, htr235c, htr357a])
                    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc567xy, htr156c, htr157a, htr168a, htr568a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                      linarith only [hlam, hc023yz, htr035a, htr235c, htr257a, htr357a])
                    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hc023yz, hc567xy, htr036a, htr136b, htr168a, htr234a, htr256c, htr257a, htr268a, htr345a, htr456a])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hd01a, hd78b, htr012a, htr125a, htr257a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hc567xy, htr047b, htr078a, htr456a, htr457b, htr578a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, htr017c, htr078a, htr178a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd01a, hd89b, htr012a, htr126a, htr268a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc023yz, hc678zy, htr038a, htr138b, htr189a, htr234a, htr347a, htr478a, htr689a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                      linarith only [hlam, hc023yz, hc678zy, htr038a, htr234a, htr347a, htr389a, htr478a, htr689a])
                    obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, hc023yz, htr038b, htr089a, htr234a, htr348c, htr389a])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd23b, hd89a, htr234a, htr347a, htr478a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hd23b, hd78a, htr234a, htr348a, htr489a, htr789a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, hc567xy, htr057a, htr058c, htr089a, htr456b, htr468b, htr489a])
                    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                    rcases m.htr 4 5 8 (by decide) (by decide) with
                      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                    ·
                      linarith only [hlam, hc567xy, htr157c, htr178c, htr189a, htr456a, htr458b, htr489a]
                    ·
                      linarith only [hlam, htr045b, htr058a, htr458a]
                  ·
                    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                      linarith only [hlam, htr135b, htr157a, htr345b, htr457a])
                    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hd23b, hd78a, htr234a, htr345a, htr457a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                      linarith only [hlam, hd23b, hd79a, htr234a, htr345a, htr457a, htr579a])
                    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                      linarith only [hlam, hd23b, hd710a, htr234a, htr345a, htr457a, htr5710a])
                    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                    rcases m.htr 4 5 8 (by decide) (by decide) with
                      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                    ·
                      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                        linarith only [hlam, hd23b, hd56a, htr235a, htr358a, htr456a, htr458a])
                      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                        linarith only [hlam, hc023yz, htr035a, htr125c, htr158a, htr235c, htr358a])
                      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                        linarith only [hlam, hc568xy, htr156c, htr158a, htr167a, htr567a])
                      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                      have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                        linarith only [hlam, hc578xy, htr157c, htr158a, htr1710a, htr5710a])
                      obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                        linarith only [hlam, hc023yz, htr035a, htr235c, htr258a, htr358a])
                      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                        linarith only [hlam, hc023yz, hc568xy, htr036a, htr136b, htr167a, htr234a, htr256c, htr258a, htr267a, htr345a, htr456a])
                      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                      rcases m.htr 6 7 10 (by decide) (by decide) with
                        ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                      ·
                        linarith only [hlam, hd01a, hd710b, htr012a, htr126a, htr267a, htr6710a]
                      ·
                        linarith only [hlam, hc023yz, hc567yz, htr037a, htr137b, htr1710a, htr234a, htr345a, htr457a, htr6710a]
                    ·
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hd23b, hd89a, htr234a, htr345a, htr458a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      rcases m.htr 3 6 7 (by decide) (by decide) with
                        ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
                      ·
                        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                          linarith only [hlam, hc013yz, htr036a, htr136c, htr167a, htr367a])
                        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                          linarith only [hlam, hc023yz, htr036a, htr236c, htr267a, htr367a])
                        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hc023yz, hc578yz, htr036a, htr234a, htr345a, htr367a, htr458a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                          linarith only [hlam, hc567yz, htr167a, htr168a, htr578a, htr678b])
                        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                          linarith only [hlam, hc023yz, hc567yz, htr036a, htr136b, htr168a, htr234a, htr267a, htr268a, htr345a, htr457a])
                        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hd01a, hd89b, htr012a, htr126a, htr268a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
                        ·
                          linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
                      ·
                        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                          linarith only [hlam, hc023yz, htr036b, htr067a, htr234a, htr346c, htr367a])
                        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                          linarith only [hlam, hc569xy, htr056c, htr059a, htr067a, htr567a])
                        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                          linarith only [hlam, htr136b, htr167a, htr367a])
                        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
                          linarith only [hlam, hd23b, hd56a, htr034c, htr045c, htr059a, htr234a, htr456a, htr459a])
                        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
                        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                          linarith only [hlam, hd23b, hd910a, htr234a, htr345a, htr459a, htr5910a])
                        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hd23b, hd57a, htr234a, htr346c, htr367a, htr578a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                          linarith only [hlam, hc156zy, htr167c, htr178a, htr567a, htr678a])
                        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                          linarith only [hlam, hd23b, hd57a, htr234a, htr346c, htr367a, htr579a, htr679a])
                        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                          linarith only [hlam, hc023yz, hc589yz, htr037a, htr137b, htr178a, htr234a, htr345a, htr459a, htr789a])
                        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                          linarith only [hlam, hc023yz, hc578yz, htr038a, htr234a, htr345a, htr389a, htr458a, htr789a])
                        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hd23b, hd56a, htr234a, htr348c, htr389a, htr568a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                          linarith only [hlam, hd23b, hd58a, htr034c, htr046c, htr068a, htr234a, htr589a, htr689a])
                        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                          linarith only [hlam, hc568yz, htr068a, htr069a, htr589a, htr689b])
                        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hd56a, hd910b, htr067a, htr069a, htr567a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hc578yz, htr589a, htr679c, htr6910a, htr789c, htr8910a]
                        ·
                          linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]
              ·
                have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                  linarith only [hlam, htr0310c, htr035b, htr0510b])
                obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, htr0310c, htr036b, htr0610b])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                  linarith only [hlam, htr035c, htr0510a, htr3510a])
                obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
                have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                  linarith only [hlam, hc5610yx, htr0310a, htr035a, htr3510b, htr356a])
                obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
                have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
                  linarith only [hlam, htr036c, htr0610a, htr3610a])
                obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
                have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                  linarith only [hlam, hd23b, hd45a, htr0310a, htr034a, htr234a, htr3510b, htr4510a])
                obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
                have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr456a, htr456b, htr456c, _, _⟩
                  linarith only [hlam, hd23b, hd510a, htr235a, htr356a, htr4510a, htr456a])
                obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
                rcases m.htr 5 6 10 (by decide) (by decide) with
                  ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                ·
                  linarith only [hlam, hd23b, hd56a, htr0310a, htr034a, htr234a, htr3610b, htr5610a]
                ·
                  linarith only [hlam, hd23b, hd610a, htr234a, htr345a, htr456a, htr5610a]
          ·
            have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr059a, htr059b, htr059c, _, _⟩
              linarith only [hlam, htr035b, htr039c, htr059b])
            obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr036b, htr039c, htr069b])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr359a, htr359b, htr359c, _, _⟩
              linarith only [hlam, htr035c, htr059a, htr359a])
            obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc569yx, htr035a, htr039a, htr356a, htr359b])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr369a, htr369b, htr369c, _, _⟩
              linarith only [hlam, htr036c, htr069a, htr369a])
            obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
            have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr459a, htr459b, htr459c, _, _⟩
              linarith only [hlam, hd23b, hd45a, htr034a, htr039a, htr234a, htr359b, htr459a])
            obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hd23b, hd59a, htr235a, htr356a, htr456a, htr459a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            rcases m.htr 5 6 9 (by decide) (by decide) with
              ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
            ·
              linarith only [hlam, hd23b, hd56a, htr034a, htr039a, htr234a, htr369b, htr569a]
            ·
              linarith only [hlam, hd23b, hd69a, htr234a, htr345a, htr456a, htr569a]
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr035b, htr038c, htr058b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr036b, htr038c, htr068b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr035c, htr058a, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc568yx, htr035a, htr038a, htr356a, htr358b])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, htr036c, htr068a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, hd23b, hd45a, htr034a, htr038a, htr234a, htr358b, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr456a, htr456b, htr456c, _, _⟩
          linarith only [hlam, hd23b, hd58a, htr235a, htr356a, htr456a, htr458a])
        obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          linarith only [hlam, hd23b, hd56a, htr034a, htr038a, htr234a, htr368b, htr568a]
        ·
          linarith only [hlam, hd23b, hd68a, htr234a, htr345a, htr456a, htr568a]
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr035b, htr037c, htr057b])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr036b, htr037c, htr067b])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr035c, htr057a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc567yx, htr035a, htr037a, htr356a, htr357b])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr036c, htr067a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hd23b, hd45a, htr034a, htr037a, htr234a, htr357b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hd23b, hd57a, htr235a, htr356a, htr456a, htr457a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd23b, hd56a, htr034a, htr037a, htr234a, htr367b, htr567a]
    ·
      linarith only [hlam, hd23b, hd67a, htr234a, htr345a, htr456a, htr567a]

theorem shard_022 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234c : m.d 2 4 < m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_022 m htr012a htr017c htr034a htr034c htr035a htr035b htr035c htr036a htr036b htr036c htr045a htr045b htr045c htr046b htr046c htr047b htr047c htr123c htr124c htr125a htr125c htr126a htr127a htr128a htr134a htr135b htr136b htr136c htr137b htr146c htr234a htr234c htr235a htr235b htr235c htr236c htr245b htr245c htr345a htr345b htr346a htr346c htr347a

#print axioms shard_022
end Jsp404.NoSatElevenDBMTerminal
