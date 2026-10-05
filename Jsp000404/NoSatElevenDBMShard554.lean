import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_554 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr028b : m.d 2 8 < m.d 0 8)
    (htr029b : m.d 2 9 < m.d 0 9)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr237c : m.d 2 7 < m.d 2 3)
    (htr238c : m.d 2 8 < m.d 2 3)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr246c : m.d 2 6 < m.d 4 6)
    (htr247c : m.d 2 7 < m.d 4 7)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr249c : m.d 2 9 < m.d 4 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  obtain ⟨hd05a, hd05braw⟩ := m.hrange 0 5 (by decide)
  have hd05b : m.d 0 5 < 4*lam := by
    linarith only [hd05braw, hp]
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
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
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hc024zy, htr046a, htr124a, htr126a, htr246c])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  rcases m.htr 1 2 7 (by decide) (by decide) with
    ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc024zy, htr047a, htr124a, htr127a, htr247c])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    rcases m.htr 1 2 8 (by decide) (by decide) with
      ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
    ·
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc024zy, htr048a, htr124a, htr128a, htr248c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      rcases m.htr 1 2 9 (by decide) (by decide) with
        ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
      ·
        have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr049a, htr049b, htr049c, _, _⟩
          linarith only [hlam, hc024zy, htr049a, htr124a, htr129a, htr249c])
        obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
        rcases m.htr 1 2 10 (by decide) (by decide) with
          ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
        ·
          rcases m.htr 2 5 6 (by decide) (by decide) with
            ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hd05b, hd24a, htr056a, htr124a, htr125a, htr256a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hd24a, hd45b, htr124a, htr125a, htr256a, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd24a, hd67b, htr124a, htr125a, htr256a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hd24a, hd56b, htr124a, htr126a, htr267a, htr567a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd24a, hd68b, htr124a, htr125a, htr256a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, hd24a, hd56b, htr124a, htr126a, htr268a, htr568a])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr569a, htr569b, htr569c, _, _⟩
              linarith only [hlam, hd24a, hd69b, htr124a, htr125a, htr256a, htr569a])
            obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
            have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr269a, htr269b, htr269c, _, _⟩
              linarith only [hlam, hd24a, hd56b, htr124a, htr126a, htr269a, htr569a])
            obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
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
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc567zy, htr045c, htr058a, htr457a, htr578b, htr678a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd02b, hd67a, htr023a, htr236c, htr268a, htr367a, htr368a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd24a, hd89b, htr025b, htr058a, htr124a, htr125a, htr589a])
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
                  linarith only [hlam, hd02b, hd68a, htr023a, htr237c, htr278a, htr689a, htr789a]
              ·
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hd01b, hd78a, htr013a, htr136a, htr367a, htr678a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd02b, hd68a, htr023a, htr236c, htr267a, htr367a, htr368a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc356yz, htr056a, htr058a, htr368a, htr568b])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd24a, hd89b, htr025b, htr058a, htr124a, htr125a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc356yz, htr368a, htr568c, htr589a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd02b, hd78a, htr023a, htr236c, htr268a, htr689a, htr789a]
                ·
                  linarith only [hlam, hd02b, hd89a, htr023a, htr236c, htr267a, htr678a, htr789a]
            ·
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc356yz, htr367a, htr456a, htr457a, htr567b])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd02b, hd67a, htr023a, htr236c, htr268a, htr367a, htr368a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                linarith only [hlam, hd02b, hd67a, htr023a, htr236c, htr269a, htr367a, htr369a])
              obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd01b, hd78a, htr013a, htr136a, htr367a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr578a, htr678a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc567yx, htr047c, htr078a, htr456a, htr457c, htr578a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd01b, hd79a, htr013a, htr136a, htr367a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr579a, htr679a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hc567yx, htr047c, htr079a, htr456a, htr457c, htr579a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
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
                linarith only [hlam, hd24a, hd89b, htr027b, htr078a, htr124a, htr127a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd24a, hd910b, htr027b, htr079a, htr124a, htr127a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
              ·
                linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
          ·
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, htr025b, htr056a, htr256a])
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
                linarith only [hlam, hd02b, hd57a, htr023a, htr235c, htr256a, htr356a, htr357a])
              obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
              have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                linarith only [hlam, hd02b, hd58a, htr023a, htr235c, htr256a, htr356a, htr358a])
              obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
              have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr359a, htr359b, htr359c, _, _⟩
                linarith only [hlam, hd02b, hd59a, htr023a, htr235c, htr256a, htr356a, htr359a])
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
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, htr145c, htr157a, htr457a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hc245xy, htr026b, htr067a, htr124a, htr126a, htr256a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc678yx, htr245c, htr256a, htr457a, htr567c, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc035zy, htr056c, htr068a, htr356a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hc679yx, htr245c, htr256a, htr457a, htr567c, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hc035zy, htr056c, htr069a, htr356a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd24a, hd78b, htr124a, htr125a, htr245c, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc567xy, htr156a, htr157b, htr178a, htr578a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd24a, hd79b, htr124a, htr125a, htr245c, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc567xy, htr156a, htr157b, htr179a, htr579a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
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
                  linarith only [hlam, hd24a, hd89b, htr026b, htr068a, htr124a, htr126a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hd24a, hd68b, htr124a, htr128a, htr289a, htr689a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd24a, hd910b, htr026b, htr069a, htr124a, htr126a, htr6910a])
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
                    linarith only [hlam, hd01b, hd78a, htr017a, htr179a, htr378a, htr379a])
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
                    linarith only [hlam, hd02b, hd79a, htr023a, htr238c, htr289a, htr7910a, htr8910a]
                ·
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                    linarith only [hlam, hd01b, hd79a, htr017a, htr178a, htr378a, htr379a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hc367yz, htr379a, htr679c, htr6910a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd01b, hd89a, htr017a, htr179a, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hd01b, hd910a, htr017a, htr178a, htr789a, htr8910a]
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc345yz, htr025b, htr057a, htr256a, htr356a, htr457a])
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
                  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                    linarith only [hlam, hc245xy, htr026b, htr068a, htr124a, htr126a, htr256a, htr568a])
                  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, hc678xy, htr245c, htr256a, htr458a, htr567a, htr568c])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, hc035zy, htr056c, htr067a, htr356a, htr567a])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    linarith only [hlam, hd24a, hd78b, htr026b, htr067a, htr124a, htr126a, htr678a]
                  ·
                    linarith only [hlam, hd24a, hd67b, htr027b, htr078a, htr124a, htr127a, htr678a]
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
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc245xy, htr026b, htr069a, htr124a, htr126a, htr256a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hc679xy, htr245c, htr256a, htr459a, htr567a, htr569c])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                      linarith only [hlam, hc035zy, htr056c, htr067a, htr356a, htr567a])
                    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                    rcases m.htr 6 7 9 (by decide) (by decide) with
                      ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                    ·
                      linarith only [hlam, hd24a, hd79b, htr026b, htr067a, htr124a, htr126a, htr679a]
                    ·
                      linarith only [hlam, hd24a, hd67b, htr027b, htr079a, htr124a, htr127a, htr679a]
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
                      have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                        linarith only [hlam, hc245xy, htr026b, htr0610a, htr124a, htr126a, htr256a, htr5610a])
                      obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc6710xy, htr245c, htr256a, htr4510a, htr5610c, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                        linarith only [hlam, hc035zy, htr056c, htr067a, htr356a, htr567a])
                      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                      rcases m.htr 6 7 10 (by decide) (by decide) with
                        ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                      ·
                        linarith only [hlam, hd24a, hd710b, htr026b, htr067a, htr124a, htr126a, htr6710a]
                      ·
                        linarith only [hlam, hd24a, hd67b, htr027b, htr0710a, htr124a, htr127a, htr6710a]
                    ·
                      rcases m.htr 5 6 7 (by decide) (by decide) with
                        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                      ·
                        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                          linarith only [hlam, hc035zy, htr056c, htr067a, htr356a, htr567a])
                        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hd24a, hd78b, htr026b, htr067a, htr124a, htr126a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                          linarith only [hlam, hd24a, hd67b, htr027b, htr078a, htr124a, htr127a, htr678a])
                        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc345yz, htr047c, htr078a, htr357a, htr457c, htr578a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                          linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
                        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                          linarith only [hlam, hd24a, hd79b, htr026b, htr067a, htr124a, htr126a, htr679a])
                        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, hd24a, hd67b, htr027b, htr079a, htr124a, htr127a, htr679a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc345yz, htr047c, htr079a, htr157b, htr179a, htr357a, htr457c])
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
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, hc345yz, htr048c, htr089a, htr358a, htr458c, htr589a])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hd01b, hd910a, htr013a, htr137a, htr379a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                          linarith only [hlam, hd01b, hd79a, htr015a, htr159a, htr5910a, htr7910a])
                        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                          linarith only [hlam, hc345yz, htr049c, htr0910a, htr359a, htr459c, htr5910a])
                        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd24a, hd910b, htr028b, htr089a, htr124a, htr128a, htr8910a]
                        ·
                          linarith only [hlam, hd24a, hd89b, htr029b, htr0910a, htr124a, htr129a, htr8910a]
                      ·
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hd02b, hd78a, htr023a, htr235c, htr256a, htr567a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hd01b, hd67a, htr015a, htr157a, htr578a, htr678a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                          linarith only [hlam, hc345yz, htr047c, htr078a, htr357a, htr457c, htr578a])
                        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                          linarith only [hlam, hd02b, hd79a, htr023a, htr235c, htr256a, htr567a, htr679a])
                        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hd01b, hd67a, htr015a, htr157a, htr579a, htr679a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, hc345yz, htr047c, htr079a, htr357a, htr457c, htr579a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                          linarith only [hlam, hd24a, hd89b, htr027b, htr078a, htr124a, htr127a, htr789a])
                        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, hd24a, hd78b, htr028b, htr089a, htr124a, htr128a, htr789a])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc345yz, htr048c, htr089a, htr358a, htr458c, htr589a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hd24a, hd910b, htr027b, htr079a, htr124a, htr127a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                          linarith only [hlam, hd24a, hd79b, htr029b, htr0910a, htr124a, htr129a, htr7910a])
                        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                          linarith only [hlam, hc345yz, htr049c, htr0910a, htr359a, htr459c, htr5910a])
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
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hd24a, hd67b, htr027b, htr078a, htr124a, htr127a, htr678a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hd24a, hd67b, htr124a, htr127a, htr278a, htr678a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
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
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, hc567xy, htr156c, htr157a, htr168a, htr568a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hd24a, hd67b, htr046c, htr068a, htr124a, htr126b, htr168a, htr467a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                    linarith only [hlam, hd02b, hd56a, htr023a, htr235c, htr257a, htr356a, htr357a])
                  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hd05b, hd24a, htr057a, htr124a, htr125a, htr257a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hd02b, hd56a, htr023a, htr237c, htr278a, htr356a, htr357b, htr378a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd24a, hd89b, htr026b, htr068a, htr124a, htr126a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, hd24a, hd68b, htr028b, htr089a, htr124a, htr128a, htr689a])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hd24a, hd68b, htr124a, htr128a, htr289a, htr689a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
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
                    linarith only [hlam, hc567xy, htr028b, htr057a, htr058c, htr289a, htr356b, htr368b, htr389a])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  rcases m.htr 3 5 8 (by decide) (by decide) with
                    ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
                  ·
                    linarith only [hlam, hc567xy, htr057c, htr078c, htr089a, htr356a, htr358b, htr389a]
                  ·
                    linarith only [hlam, htr035b, htr058a, htr358a]
                ·
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, htr135b, htr157a, htr357a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, htr157c, htr158b, htr178c])
                  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                    linarith only [hlam, hd01b, hd56a, htr015a, htr158a, htr356a, htr358a])
                  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc567yz, htr046c, htr068a, htr467a, htr578a, htr678b])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd01b, hd89a, htr013a, htr135a, htr358a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hd24a, hd89b, htr026b, htr068a, htr124a, htr126a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
                  ·
                    linarith only [hlam, hd02b, hd58a, htr023a, htr237c, htr278a, htr589a, htr789a]
              ·
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, hd24a, hd46b, htr026b, htr067a, htr124a, htr126a, htr467a])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc568xy, htr056c, htr058a, htr067a, htr567a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                  linarith only [hlam, hc569xy, htr056c, htr059a, htr067a, htr567a])
                obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                  linarith only [hlam, hd05b, hd24a, htr058a, htr124a, htr125a, htr258a])
                obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr259a, htr259b, htr259c, _, _⟩
                  linarith only [hlam, hd05b, hd24a, htr059a, htr124a, htr125a, htr259a])
                obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, hc456zy, htr356a, htr357a, htr467a, htr567c])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                  linarith only [hlam, hd02b, hd56a, htr023a, htr235c, htr258a, htr356a, htr358a])
                obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr359a, htr359b, htr359c, _, _⟩
                  linarith only [hlam, hd02b, hd56a, htr023a, htr235c, htr259a, htr356a, htr359a])
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
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hc456zy, htr047c, htr078a, htr467c, htr567a, htr678a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc456zy, htr467a, htr567b, htr579a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd24a, hd89b, htr027b, htr078a, htr124a, htr127a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hd24a, hd78b, htr124a, htr128a, htr289a, htr789a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd02b, hd56a, htr023a, htr238c, htr289a, htr568a, htr689a])
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
                  linarith only [hlam, hd24a, hd910b, htr026b, htr069a, htr124a, htr126a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hc578yz, htr589a, htr679c, htr6910a, htr789c, htr8910a]
                ·
                  linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]
        ·
          have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
            linarith only [hlam, htr1210c, htr125b, htr1510b])
          obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
          have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
            linarith only [hlam, htr1210c, htr126b, htr1610b])
          obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
          have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
            linarith only [hlam, htr125c, htr1510a, htr2510a])
          obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc5610yx, htr1210a, htr125a, htr2510b, htr256a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
            linarith only [hlam, htr126c, htr1610a, htr2610a])
          obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
          have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
            linarith only [hlam, hd02b, hd35a, htr023a, htr1210a, htr123a, htr2510b, htr3510a])
          obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hd02b, hd510a, htr023a, htr235c, htr256a, htr3510a, htr356a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          rcases m.htr 5 6 10 (by decide) (by decide) with
            ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
          ·
            linarith only [hlam, hd02b, hd56a, htr023a, htr1210a, htr123a, htr2610b, htr5610a]
          ·
            linarith only [hlam, hd01b, hd610a, htr013a, htr135a, htr356a, htr5610a]
      ·
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, htr125b, htr129c, htr159b])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, htr126b, htr129c, htr169b])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr259a, htr259b, htr259c, _, _⟩
          linarith only [hlam, htr125c, htr159a, htr259a])
        obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc569yx, htr125a, htr129a, htr256a, htr259b])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, htr126c, htr169a, htr269a])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hd02b, hd35a, htr023a, htr123a, htr129a, htr259b, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hd02b, hd59a, htr023a, htr235c, htr256a, htr356a, htr359a])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        rcases m.htr 5 6 9 (by decide) (by decide) with
          ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
        ·
          linarith only [hlam, hd02b, hd56a, htr023a, htr123a, htr129a, htr269b, htr569a]
        ·
          linarith only [hlam, hd01b, hd69a, htr013a, htr135a, htr356a, htr569a]
    ·
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr125b, htr128c, htr158b])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr126b, htr128c, htr168b])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr258a, htr258b, htr258c, _, _⟩
        linarith only [hlam, htr125c, htr158a, htr258a])
      obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc568yx, htr125a, htr128a, htr256a, htr258b])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr126c, htr168a, htr268a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hd02b, hd35a, htr023a, htr123a, htr128a, htr258b, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hd02b, hd58a, htr023a, htr235c, htr256a, htr356a, htr358a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        linarith only [hlam, hd02b, hd56a, htr023a, htr123a, htr128a, htr268b, htr568a]
      ·
        linarith only [hlam, hd01b, hd68a, htr013a, htr135a, htr356a, htr568a]
  ·
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr125b, htr127c, htr157b])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr126b, htr127c, htr167b])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, htr125c, htr157a, htr257a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hc567yx, htr125a, htr127a, htr256a, htr257b])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, htr126c, htr167a, htr267a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd02b, hd35a, htr023a, htr123a, htr127a, htr257b, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd02b, hd57a, htr023a, htr235c, htr256a, htr356a, htr357a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd02b, hd56a, htr023a, htr123a, htr127a, htr267b, htr567a]
    ·
      linarith only [hlam, hd01b, hd67a, htr013a, htr135a, htr356a, htr567a]

theorem shard_554 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr028b : m.d 2 8 < m.d 0 8)
    (htr029b : m.d 2 9 < m.d 0 9)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr237c : m.d 2 7 < m.d 2 3)
    (htr238c : m.d 2 8 < m.d 2 3)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr246c : m.d 2 6 < m.d 4 6)
    (htr247c : m.d 2 7 < m.d 4 7)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr249c : m.d 2 9 < m.d 4 9)
    : False :=
  proof_shard_554 m htr013a htr015a htr017a htr023a htr025b htr026b htr027b htr028b htr029b htr035b htr045c htr123a htr124a htr125a htr125b htr125c htr126a htr126b htr126c htr135a htr135b htr136a htr137a htr138a htr145c htr235c htr236c htr237c htr238c htr245c htr246c htr247c htr248c htr249c

#print axioms shard_554
end Jsp404.NoSatElevenDBMTerminal
