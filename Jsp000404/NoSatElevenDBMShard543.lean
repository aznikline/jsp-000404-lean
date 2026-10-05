import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_543 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr037c : m.d 0 7 < m.d 0 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd24a := (m.hrange 2 4 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
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
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  have hd610a := (m.hrange 6 10 (by decide)).1
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
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc248xy, hc248yx, hc248yz, hc248zy⟩ := endpoint_caps m 2 4 8 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
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
  have hforced025 := (m.htr 0 2 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr025a, htr025b, htr025c, _, _⟩
    linarith only [hlam, hc234yx, htr023a, htr025a, htr124a, htr125a])
  obtain ⟨htr025a, htr025b, htr025c, _, _⟩ := hforced025
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, htr024c, htr025b, htr045c])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, htr014b, htr045a, htr124b, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hc456yx, htr012b, htr025a, htr124a, htr245c, htr246a])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hc234yx, htr023a, htr024c, htr046a, htr246a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc457yx, htr012b, htr025a, htr124a, htr245c, htr247a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc458yx, htr012b, htr025a, htr124a, htr245c, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, hc459yx, htr012b, htr025a, htr124a, htr245c, htr249a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  rcases m.htr 1 2 6 (by decide) (by decide) with
    ⟨htr126a, htr126b, htr126c, _, _⟩ | ⟨htr126a, htr126b, htr126c, _, _⟩
  ·
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, hc234yx, htr023a, htr026a, htr124a, htr126a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    rcases m.htr 1 2 7 (by decide) (by decide) with
      ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
    ·
      rcases m.htr 1 2 8 (by decide) (by decide) with
        ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
      ·
        rcases m.htr 1 2 9 (by decide) (by decide) with
          ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
        ·
          rcases m.htr 1 2 10 (by decide) (by decide) with
            ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
          ·
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd24a, hd67b, htr124a, htr125a, htr245c, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hd24a, hd56b, htr124a, htr126a, htr267a, htr567a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc246xy, htr124a, htr126b, htr167a, htr267a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd24a, hd68b, htr124a, htr125a, htr245c, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hd24a, hd56b, htr124a, htr126a, htr268a, htr568a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc246xy, htr124a, htr126b, htr168a, htr268a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                linarith only [hlam, hd24a, hd69b, htr124a, htr125a, htr245c, htr456a, htr569a])
              obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, hd24a, hd56b, htr124a, htr126a, htr269a, htr569a])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc246xy, htr124a, htr126b, htr169a, htr269a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd24a, hd78b, htr124a, htr125a, htr245c, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hd24a, hd57b, htr124a, htr127a, htr278a, htr578a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc247xy, htr124a, htr127b, htr178a, htr278a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, hc567zy, htr245c, htr258a, htr457a, htr578b, htr678a])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                    linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
                  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hd01b, hd67a, htr016a, htr168a, htr367a, htr368a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd24a, hd89b, htr124a, htr125a, htr258a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd01b, hd89a, htr013a, htr136a, htr368a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a]
                  ·
                    linarith only [hlam, hd01b, hd68a, htr017a, htr178a, htr689a, htr789a]
                ·
                  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                    linarith only [hlam, hd01b, hd78a, htr013a, htr136a, htr367a, htr678a])
                  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                    linarith only [hlam, hd01b, hd68a, htr016a, htr167a, htr367a, htr368a])
                  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, hc356yz, htr245c, htr258a, htr368a, htr456a, htr568b])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd24a, hd89b, htr124a, htr125a, htr258a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc356yz, htr368a, htr568c, htr589a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd01b, hd78a, htr016a, htr168a, htr689a, htr789a]
                  ·
                    linarith only [hlam, hd01b, hd89a, htr016a, htr167a, htr678a, htr789a]
              ·
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc356yz, htr367a, htr456a, htr457a, htr567b])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd01b, hd67a, htr016a, htr168a, htr367a, htr368a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                  linarith only [hlam, hd01b, hd67a, htr016a, htr169a, htr367a, htr369a])
                obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd01b, hd78a, htr013a, htr136a, htr367a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr578a, htr678a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc567yx, htr247c, htr278a, htr456a, htr457c, htr578a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hd01b, hd79a, htr013a, htr136a, htr367a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr579a, htr679a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, hc567yx, htr247c, htr279a, htr456a, htr457c, htr579a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd01b, hd89a, htr013a, htr136a, htr368a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd01b, hd910a, htr013a, htr136a, htr369a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd24a, hd89b, htr124a, htr127a, htr278a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hd24a, hd910b, htr124a, htr127a, htr279a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
                ·
                  linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
            ·
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hd24a, hd45b, htr124a, htr125a, htr256a, htr456a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, hc245xy, htr015b, htr056a, htr124a, htr125b, htr256a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hc245xy, htr124a, htr125b, htr156a, htr256a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              rcases m.htr 3 5 6 (by decide) (by decide) with
                ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
              ·
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, hd01b, hd57a, htr015a, htr156a, htr356a, htr357a])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                  linarith only [hlam, hd01b, hd58a, htr015a, htr156a, htr356a, htr358a])
                obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr359a, htr359b, htr359c, _, _⟩
                  linarith only [hlam, hd01b, hd59a, htr015a, htr156a, htr356a, htr359a])
                obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
                rcases m.htr 4 5 7 (by decide) (by decide) with
                  ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, htr045c, htr057a, htr457a])
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
                    linarith only [hlam, hc678yx, htr245c, htr256a, htr457a, htr567c, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, hc345yz, htr246c, htr268a, htr356a, htr456c, htr568a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                    linarith only [hlam, hc679yx, htr245c, htr256a, htr457a, htr567c, htr569a])
                  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                    linarith only [hlam, hc345yz, htr246c, htr269a, htr356a, htr456c, htr569a])
                  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                    linarith only [hlam, hc6710yx, htr245c, htr256a, htr457a, htr5610a, htr567c])
                  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                    linarith only [hlam, hc345yz, htr246c, htr2610a, htr356a, htr456c, htr5610a])
                  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd24a, hd78b, htr124a, htr125a, htr245c, htr457a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, hc567xy, htr056a, htr057b, htr078a, htr578a])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd24a, hd79b, htr124a, htr125a, htr245c, htr457a, htr579a])
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
                    linarith only [hlam, hd24a, hd89b, htr124a, htr126a, htr268a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hd24a, hd68b, htr124a, htr128a, htr289a, htr689a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hd24a, hd910b, htr124a, htr126a, htr269a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, hc234yx, hc678zy, htr023c, htr037c, htr079a, htr124a, htr126a, htr268a, htr378a, htr379a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hd01b, hd910a, htr013a, htr137a, htr379a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
                    ·
                      linarith only [hlam, hc248xy, hc679zy, htr124a, htr126a, htr269a, htr289a, htr7910a, htr8910a]
                  ·
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, hc234yx, hc679zy, htr023c, htr037c, htr078a, htr124a, htr126a, htr269a, htr378a, htr379a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hc367yz, htr379a, htr679c, htr6910a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc234yx, hc689zy, htr023c, htr037c, htr079a, htr124a, htr126a, htr269a, htr7910a, htr8910a]
                    ·
                      linarith only [hlam, hc234yx, hc6910zy, htr023c, htr037c, htr078a, htr124a, htr126a, htr2610a, htr789a, htr8910a]
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hc345yz, htr015b, htr057a, htr156a, htr356a, htr457a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hc345yz, htr156a, htr157a, htr356a, htr457a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  rcases m.htr 4 5 8 (by decide) (by decide) with
                    ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                  ·
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, htr045c, htr058a, htr458a])
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
                      linarith only [hlam, hc247xy, htr017b, htr078a, htr124a, htr127b, htr278a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, htr056b, htr068a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hc678xy, htr245c, htr256a, htr458a, htr567a, htr568c])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                      linarith only [hlam, hc345yz, htr246c, htr267a, htr356a, htr456c, htr567a])
                    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd24a, hd78b, htr124a, htr126a, htr267a, htr678a]
                    ·
                      linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr278a, htr678a]
                  ·
                    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                      linarith only [hlam, hc345yz, htr156a, htr158a, htr356a, htr458a])
                    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                    rcases m.htr 4 5 9 (by decide) (by decide) with
                      ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
                    ·
                      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                        linarith only [hlam, htr045c, htr059a, htr459a])
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
                        linarith only [hlam, hc247xy, htr017b, htr079a, htr124a, htr127b, htr279a])
                      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, htr056b, htr069a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc679xy, htr245c, htr256a, htr459a, htr567a, htr569c])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                        linarith only [hlam, hc345yz, htr246c, htr267a, htr356a, htr456c, htr567a])
                      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                      rcases m.htr 6 7 9 (by decide) (by decide) with
                        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                      ·
                        linarith only [hlam, hd24a, hd79b, htr124a, htr126a, htr267a, htr679a]
                      ·
                        linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr279a, htr679a]
                    ·
                      have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr159a, htr159b, htr159c, _, _⟩
                        linarith only [hlam, hc345yz, htr156a, htr159a, htr356a, htr459a])
                      obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
                      rcases m.htr 4 5 10 (by decide) (by decide) with
                        ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                      ·
                        have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                          linarith only [hlam, htr045c, htr0510a, htr4510a])
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
                          linarith only [hlam, hc247xy, htr017b, htr0710a, htr124a, htr127b, htr2710a])
                        obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                        have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                          linarith only [hlam, htr056b, htr0610a, htr5610a])
                        obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc6710xy, htr245c, htr256a, htr4510a, htr5610c, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                          linarith only [hlam, hc345yz, htr246c, htr267a, htr356a, htr456c, htr567a])
                        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                        rcases m.htr 6 7 10 (by decide) (by decide) with
                          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                        ·
                          linarith only [hlam, hd24a, hd710b, htr124a, htr126a, htr267a, htr6710a]
                        ·
                          linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr2710a, htr6710a]
                      ·
                        rcases m.htr 5 6 7 (by decide) (by decide) with
                          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                        ·
                          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                            linarith only [hlam, hc345yz, htr246c, htr267a, htr356a, htr456c, htr567a])
                          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                            linarith only [hlam, hd24a, hd78b, htr124a, htr126a, htr267a, htr678a])
                          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                            linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr278a, htr678a])
                          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hc345yz, htr247c, htr278a, htr357a, htr457c, htr578a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                            linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
                          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hd24a, hd79b, htr124a, htr126a, htr267a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                            linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr279a, htr679a])
                          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                            linarith only [hlam, hc247xy, htr124a, htr127b, htr179a, htr279a])
                          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                            linarith only [hlam, hd01b, hd78a, htr017a, htr179a, htr378a, htr379a])
                          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hd01b, hd89a, htr015a, htr157a, htr578a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hd01b, hd78a, htr015a, htr158a, htr589a, htr789a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                            linarith only [hlam, hc345yz, htr248c, htr289a, htr358a, htr458c, htr589a])
                          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                            linarith only [hlam, hd01b, hd910a, htr013a, htr137a, htr379a, htr7910a])
                          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                            linarith only [hlam, hd01b, hd79a, htr015a, htr159a, htr5910a, htr7910a])
                          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                            linarith only [hlam, hc345yz, htr249c, htr2910a, htr359a, htr459c, htr5910a])
                          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd24a, hd910b, htr124a, htr128a, htr289a, htr8910a]
                          ·
                            linarith only [hlam, hd24a, hd89b, htr124a, htr129a, htr2910a, htr8910a]
                        ·
                          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                            linarith only [hlam, hd01b, hd78a, htr015a, htr156a, htr567a, htr678a])
                          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                            linarith only [hlam, hd01b, hd67a, htr015a, htr157a, htr578a, htr678a])
                          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                            linarith only [hlam, hc345yz, htr247c, htr278a, htr357a, htr457c, htr578a])
                          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hd01b, hd79a, htr015a, htr156a, htr567a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                            linarith only [hlam, hd01b, hd67a, htr015a, htr157a, htr579a, htr679a])
                          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                            linarith only [hlam, hc345yz, htr247c, htr279a, htr357a, htr457c, htr579a])
                          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hd24a, hd89b, htr124a, htr127a, htr278a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                            linarith only [hlam, hd24a, hd78b, htr124a, htr128a, htr289a, htr789a])
                          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc345yz, htr248c, htr289a, htr358a, htr458c, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                            linarith only [hlam, hd24a, hd910b, htr124a, htr127a, htr279a, htr7910a])
                          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                          have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                            linarith only [hlam, hd24a, hd79b, htr124a, htr129a, htr2910a, htr7910a])
                          obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                            linarith only [hlam, hc345yz, htr249c, htr2910a, htr359a, htr459c, htr5910a])
                          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd01b, hd89a, htr015a, htr159a, htr5910a, htr8910a]
                          ·
                            linarith only [hlam, hd01b, hd910a, htr015a, htr158a, htr589a, htr8910a]
              ·
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd01b, hd67a, htr013a, htr135a, htr356a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd01b, hd68a, htr013a, htr135a, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd01b, hd56a, htr013a, htr136a, htr368a, htr568a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                rcases m.htr 4 6 7 (by decide) (by decide) with
                  ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                ·
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd24a, hd78b, htr124a, htr126a, htr246c, htr467a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr278a, htr678a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, hc247xy, htr017b, htr078a, htr124a, htr127b, htr278a])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hc247xy, htr124a, htr127b, htr178a, htr278a])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  rcases m.htr 3 5 7 (by decide) (by decide) with
                    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                  ·
                    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                      linarith only [hlam, hd01b, hd56a, htr015a, htr157a, htr356a, htr357a])
                    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hc234yx, htr023c, htr035c, htr057a, htr124a, htr125b, htr157a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                      linarith only [hlam, hc567xy, htr056c, htr057a, htr068a, htr568a])
                    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                      linarith only [hlam, hc245xy, htr124a, htr125b, htr157a, htr257a])
                    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hc246xy, htr016b, htr068a, htr124a, htr126b, htr268a])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hd01b, hd56a, htr017a, htr178a, htr356a, htr357b, htr378a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd24a, hd89b, htr124a, htr126a, htr268a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hd24a, hd68b, htr124a, htr128a, htr289a, htr689a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc248xy, htr124a, htr128b, htr189a, htr289a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                      linarith only [hlam, hd01b, hd78a, htr013a, htr138a, htr389a, htr789a])
                    obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, hc567xy, htr018b, htr057a, htr058c, htr189a, htr356b, htr368b, htr389a])
                    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                    rcases m.htr 3 5 8 (by decide) (by decide) with
                      ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
                    ·
                      linarith only [hlam, hc248xy, hc567xy, htr124a, htr125a, htr257a, htr289a, htr356a, htr358b, htr389a]
                    ·
                      linarith only [hlam, htr035b, htr058a, htr358a]
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, htr035b, htr057a, htr357a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                      linarith only [hlam, htr057c, htr058b, htr078c])
                    obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                      linarith only [hlam, hc234yx, hc567yz, htr023c, htr035c, htr058a, htr124a, htr126a, htr246c, htr357a, htr358a, htr467a])
                    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                      linarith only [hlam, hc567yz, htr246c, htr268a, htr467a, htr578a, htr678b])
                    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hd01b, hd89a, htr013a, htr135a, htr358a, htr589a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd24a, hd89b, htr124a, htr126a, htr268a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
                    ·
                      linarith only [hlam, hd01b, hd58a, htr017a, htr178a, htr589a, htr789a]
                ·
                  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                    linarith only [hlam, hd24a, hd46b, htr124a, htr126a, htr267a, htr467a])
                  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, hc246xy, htr016b, htr067a, htr124a, htr126b, htr267a])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hc568xy, htr056c, htr058a, htr067a, htr567a])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                    linarith only [hlam, hc569xy, htr056c, htr059a, htr067a, htr567a])
                  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, hc234yx, htr023c, htr035c, htr058a, htr124a, htr125b, htr158a])
                  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
                    linarith only [hlam, hc234yx, htr023c, htr035c, htr059a, htr124a, htr125b, htr159a])
                  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
                  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                    linarith only [hlam, hc456zy, htr356a, htr357a, htr467a, htr567c])
                  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                    linarith only [hlam, hd01b, hd56a, htr015a, htr158a, htr356a, htr358a])
                  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
                    linarith only [hlam, hd01b, hd56a, htr015a, htr159a, htr356a, htr359a])
                  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd01b, hd79a, htr013a, htr135a, htr357a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd01b, hd89a, htr013a, htr135a, htr358a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                    linarith only [hlam, hd01b, hd910a, htr013a, htr135a, htr359a, htr5910a])
                  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc456zy, htr247c, htr278a, htr467c, htr567a, htr678a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456zy, htr467a, htr567b, htr579a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd24a, hd89b, htr124a, htr127a, htr278a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hd24a, hd78b, htr124a, htr128a, htr289a, htr789a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc248xy, htr124a, htr128b, htr189a, htr289a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd01b, hd56a, htr018a, htr189a, htr568a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc056zy, htr068a, htr568b, htr589a, htr689a])
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
            have hforced0210 := (m.htr 0 2 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0210a, htr0210b, htr0210c, _, _⟩
              linarith only [hlam, htr012b, htr0210a, htr1210a])
            obtain ⟨htr0210a, htr0210b, htr0210c, _, _⟩ := hforced0210
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, htr0210c, htr025b, htr0510b])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0210c, htr026b, htr0610b])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
              linarith only [hlam, htr025c, htr0510a, htr2510a])
            obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc5610yx, htr012b, htr025a, htr1210a, htr2510b, htr256a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc245xy, htr124a, htr125b, htr156a, htr256a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
              linarith only [hlam, htr026c, htr0610a, htr2610a])
            obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
            have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
              linarith only [hlam, hc235zy, htr1210a, htr125a, htr2510b, htr3510a])
            obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hd01b, hd510a, htr015a, htr156a, htr3510a, htr356a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            rcases m.htr 5 6 10 (by decide) (by decide) with
              ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            ·
              linarith only [hlam, hc256zy, htr1210a, htr126a, htr2610b, htr5610a]
            ·
              linarith only [hlam, hd01b, hd610a, htr013a, htr135a, htr356a, htr5610a]
        ·
          have hforced029 := (m.htr 0 2 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr029a, htr029b, htr029c, _, _⟩
            linarith only [hlam, htr012b, htr029a, htr129a])
          obtain ⟨htr029a, htr029b, htr029c, _, _⟩ := hforced029
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr025b, htr029c, htr059b])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr026b, htr029c, htr069b])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr259a, htr259b, htr259c, _, _⟩
            linarith only [hlam, htr025c, htr059a, htr259a])
          obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc569yx, htr012b, htr025a, htr129a, htr256a, htr259b])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc245xy, htr124a, htr125b, htr156a, htr256a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr269a, htr269b, htr269c, _, _⟩
            linarith only [hlam, htr026c, htr069a, htr269a])
          obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
          have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr359a, htr359b, htr359c, _, _⟩
            linarith only [hlam, hc235zy, htr125a, htr129a, htr259b, htr359a])
          obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hd01b, hd59a, htr015a, htr156a, htr356a, htr359a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            linarith only [hlam, hc256zy, htr126a, htr129a, htr269b, htr569a]
          ·
            linarith only [hlam, hd01b, hd69a, htr013a, htr135a, htr356a, htr569a]
      ·
        have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr028a, htr028b, htr028c, _, _⟩
          linarith only [hlam, htr012b, htr028a, htr128a])
        obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, htr025b, htr028c, htr058b])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr026b, htr028c, htr068b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr025c, htr058a, htr258a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc568yx, htr012b, htr025a, htr128a, htr256a, htr258b])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc245xy, htr124a, htr125b, htr156a, htr256a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr026c, htr068a, htr268a])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc235zy, htr125a, htr128a, htr258b, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hd01b, hd58a, htr015a, htr156a, htr356a, htr358a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          linarith only [hlam, hc256zy, htr126a, htr128a, htr268b, htr568a]
        ·
          linarith only [hlam, hd01b, hd68a, htr013a, htr135a, htr356a, htr568a]
    ·
      have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr027a, htr027b, htr027c, _, _⟩
        linarith only [hlam, htr012b, htr027a, htr127a])
      obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr025b, htr027c, htr057b])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr026b, htr027c, htr067b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr025c, htr057a, htr257a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc567yx, htr012b, htr025a, htr127a, htr256a, htr257b])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc245xy, htr124a, htr125b, htr156a, htr256a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, htr026c, htr067a, htr267a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc235zy, htr125a, htr127a, htr257b, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hd01b, hd57a, htr015a, htr156a, htr356a, htr357a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        linarith only [hlam, hc256zy, htr126a, htr127a, htr267b, htr567a]
      ·
        linarith only [hlam, hd01b, hd67a, htr013a, htr135a, htr356a, htr567a]
  ·
    have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr026a, htr026b, htr026c, _, _⟩
      linarith only [hlam, htr012b, htr026a, htr126a])
    obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
    have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr056a, htr056b, htr056c, _, _⟩
      linarith only [hlam, htr025b, htr026c, htr056b])
    obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, htr025c, htr056a, htr256a])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc567xy, htr012b, htr025a, htr126a, htr256b, htr257a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc245xy, htr124a, htr125b, htr157a, htr257a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc568xy, htr012b, htr025a, htr126a, htr256b, htr258a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hc245xy, htr124a, htr125b, htr158a, htr258a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr259a, htr259b, htr259c, _, _⟩
      linarith only [hlam, hc569xy, htr012b, htr025a, htr126a, htr256b, htr259a])
    obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
    have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr159a, htr159b, htr159c, _, _⟩
      linarith only [hlam, hc245xy, htr124a, htr125b, htr159a, htr259a])
    obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc235zy, htr125a, htr126a, htr256b, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd01b, hd56a, htr015a, htr157a, htr356a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hd01b, hd56a, htr015a, htr158a, htr356a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr359a, htr359b, htr359c, _, _⟩
      linarith only [hlam, hd01b, hd56a, htr015a, htr159a, htr356a, htr359a])
    obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hd01b, hd67a, htr013a, htr135a, htr356a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr267a, htr567a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc236yx, htr023a, htr026c, htr067a, htr267a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd01b, hd68a, htr013a, htr135a, htr356a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr268a, htr568a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc236yx, htr023a, htr026c, htr068a, htr268a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd01b, hd89a, htr013a, htr135a, htr358a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc014yx, hc578yz, htr013a, htr046a, htr135a, htr358a, htr467a, htr678a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc016yx, hc568yz, htr013a, htr067a, htr135a, htr358a, htr467a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc016yx, hc589yz, htr013a, htr067a, htr135a, htr359a, htr678a, htr789a]
      ·
        linarith only [hlam, hc016yx, hc578yz, htr013a, htr068a, htr135a, htr358a, htr689a, htr789a]
    ·
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc016yx, hc567yz, htr013a, htr068a, htr135a, htr357a, htr467a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc014yx, hc589yz, htr013a, htr046a, htr135a, htr359a, htr468a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
      ·
        linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]

theorem shard_543 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023c : m.d 0 3 < m.d 2 3)
    (htr024c : m.d 0 4 < m.d 0 2)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr037c : m.d 0 7 < m.d 0 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124b : m.d 2 4 < m.d 1 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    : False :=
  proof_shard_543 m htr012a htr012b htr013a htr014b htr015a htr015b htr016a htr016b htr017a htr017b htr018a htr018b htr023a htr023c htr024c htr035b htr035c htr037c htr124a htr124b htr125a htr125b htr135a htr136a htr137a htr138a

#print axioms shard_543
end Jsp404.NoSatElevenDBMTerminal
