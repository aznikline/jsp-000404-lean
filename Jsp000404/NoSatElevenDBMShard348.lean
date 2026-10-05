import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_348 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr1410a : m.d 1 4 + lam ≤ m.d 4 10)
    (htr156b : m.d 5 6 < m.d 1 6)
    (htr157b : m.d 5 7 < m.d 1 7)
    (htr158b : m.d 5 8 < m.d 1 8)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 4 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd16a := (m.hrange 1 6 (by decide)).1
  have hd18a := (m.hrange 1 8 (by decide)).1
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < 4*lam := by
    linarith only [hd26braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd49a, hd49braw⟩ := m.hrange 4 9 (by decide)
  have hd49b : m.d 4 9 < 4*lam := by
    linarith only [hd49braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  have hd69a := (m.hrange 6 9 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc046xy, hc046yx, hc046yz, hc046zy⟩ := endpoint_caps m 0 4 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc479xy, hc479yx, hc479yz, hc479zy⟩ := endpoint_caps m 4 7 9 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
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
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hd13b, hd56a, htr013a, htr016a, htr167a, htr567a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc136yx, htr013a, htr016c, htr067a, htr167a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            rcases m.htr 4 6 7 (by decide) (by decide) with
              ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
            ·
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc123xy, hc678yx, htr013a, htr016a, htr124a, htr168a, htr246a, htr467a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc123xy, hc679yx, htr013a, htr016a, htr124a, htr169a, htr246a, htr467a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd12a, hd78b, htr124a, htr246a, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd12a, hd79b, htr124a, htr246a, htr467a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc567yz, htr467a, htr468a, htr578a, htr678b])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd12a, hd89b, htr124a, htr246a, htr468a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hd12a, hd810b, htr124a, htr246a, htr468a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc567yz, htr158b, htr189a, htr578b, htr678a, htr789a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                  linarith only [hlam, hc123xy, hc689zy, htr013a, htr018a, htr124a, htr189a, htr246a, htr469a])
                obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  linarith only [hlam, hc567yz, htr578a, htr678c, htr6810a, htr7810a])
                obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc567yz, htr158b, htr1810a, htr578b, htr678a, htr7810a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc123xy, hc8910yz, htr013a, htr018a, htr124a, htr1810a, htr249a, htr4910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hc136yx, hc489zy, htr013a, htr018a, htr169a, htr189a, htr4910a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd67b, hd89a, htr467a, htr469a, htr6910a, htr8910a]
                ·
                  linarith only [hlam, hd13b, hd910a, htr013a, htr018a, htr189a, htr8910a]
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc123xy, hc678zy, htr013a, htr017a, htr124a, htr157b, htr246a, htr468a, htr578a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hd12a, hd67b, htr126a, htr268a, htr467a, htr468a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd13b, hd89a, htr013a, htr017a, htr157b, htr578a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd67b, hd78a, htr467a, htr468a, htr689a, htr789a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc136yx, hc478zy, htr013a, htr017a, htr157b, htr168a, htr489a, htr578a, htr689a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc123xy, hc789yz, htr013a, htr017a, htr124a, htr179a, htr248a, htr489a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc123xy, hc8910yx, htr013a, htr018a, htr124a, htr1810a, htr248a, htr489a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                  linarith only [hlam, hc167yz, htr179a, htr246c, htr269a, htr467a, htr679b])
                obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hd18a, hd67b, htr1810a, htr467a, htr468a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc136yx, hc478zy, htr013a, htr017a, htr157b, htr168a, htr4810a, htr578a, htr6810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                  linarith only [hlam, hc123xy, hc8910zy, htr013a, htr019a, htr124a, htr1910a, htr248a, htr4810a])
                obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd16a, hd910b, htr168a, htr268a, htr269a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc167yz, htr179a, htr679c, htr6910a, htr7910a]
                ·
                  linarith only [hlam, hc167yz, htr179b, htr1910a, htr679a, htr7910a]
            ·
              rcases m.htr 2 6 7 (by decide) (by decide) with
                ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hd12a, hd68b, htr126a, htr267a, htr467a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                rcases m.htr 5 6 8 (by decide) (by decide) with
                  ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc456zy, htr067a, htr068a, htr467a, htr568a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, hc456zy, htr267a, htr268a, htr467a, htr568a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  rcases m.htr 5 6 9 (by decide) (by decide) with
                    ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
                  ·
                    rcases m.htr 5 6 10 (by decide) (by decide) with
                      ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                    ·
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc123xy, hc789yx, htr013a, htr017a, htr126a, htr179a, htr267a, htr678a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc456zy, htr157b, htr179a, htr267c, htr279a, htr467a, htr567b])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hd12a, hd78b, htr127a, htr279a, htr478a, htr479a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc123xy, hc789zy, htr013a, htr018a, htr124a, htr189a, htr247a, htr479a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc456zy, htr158b, htr189a, htr468a, htr568b, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd12a, hd89b, htr126a, htr267a, htr678a, htr789a]
                        ·
                          linarith only [hlam, hd12a, hd78b, htr126a, htr268a, htr689a, htr789a]
                      ·
                        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                          linarith only [hlam, hc456zy, htr157b, htr178a, htr467a, htr567b, htr678a])
                        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                          linarith only [hlam, hc123xy, hc789xy, htr013a, htr017a, htr126a, htr178a, htr267a, htr679a])
                        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc456zy, htr157b, htr179a, htr467a, htr567b, htr679a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc123xy, hc789yz, htr013a, htr017a, htr124a, htr179a, htr248a, htr489a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                          linarith only [hlam, hc123xy, hc478zy, htr013a, htr017a, htr128a, htr178a, htr289a, htr489a])
                        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc456zy, htr158b, htr189a, htr268c, htr289a, htr468a, htr568b])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd13b, hd78a, htr013a, htr018a, htr189a, htr789a]
                        ·
                          linarith only [hlam, hd13b, hd89a, htr013a, htr017a, htr178a, htr789a]
                    ·
                      have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                        linarith only [hlam, htr056b, htr0610a, htr5610a])
                      obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, htr0610c, htr067b, htr0710b])
                      obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, htr0610c, htr068b, htr0810b])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                        linarith only [hlam, hc137yx, htr013a, htr017c, htr0710a, htr1710a])
                      obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                        linarith only [hlam, hc138yx, htr013a, htr018c, htr0810a, htr1810a])
                      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc123xy, hc7810yx, htr013a, htr017a, htr126a, htr1710a, htr267a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                        linarith only [hlam, hc456zy, htr157b, htr178a, htr467a, htr567b, htr678a])
                      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                      rcases m.htr 7 8 10 (by decide) (by decide) with
                        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      ·
                        linarith only [hlam, hd13b, hd78a, htr013a, htr018a, htr1810a, htr7810a]
                      ·
                        linarith only [hlam, hd13b, hd810a, htr013a, htr017a, htr178a, htr7810a]
                  ·
                    have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                      linarith only [hlam, htr056b, htr069a, htr569a])
                    obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, htr067b, htr069c, htr079b])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr068b, htr069c, htr089b])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                      linarith only [hlam, hc137yx, htr013a, htr017c, htr079a, htr179a])
                    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc138yx, htr013a, htr018c, htr089a, htr189a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc123xy, hc789yx, htr013a, htr017a, htr126a, htr179a, htr267a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc456zy, htr157b, htr178a, htr467a, htr567b, htr678a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd13b, hd78a, htr013a, htr018a, htr189a, htr789a]
                    ·
                      linarith only [hlam, hd13b, hd89a, htr013a, htr017a, htr178a, htr789a]
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, htr056b, htr068a, htr568a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, htr067b, htr068c, htr078b])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, htr026c, htr056b, htr268a, htr568a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc123xy, hc789xy, htr013a, htr017a, htr126a, htr178a, htr267a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc456zy, htr157b, htr179a, htr467a, htr567b, htr679a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc123xy, hc789yz, htr013a, htr017a, htr124a, htr179a, htr248a, htr489a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc123xy, hc468zy, htr013a, htr016a, htr128a, htr156b, htr289a, htr489a, htr568a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd46b, hd78a, htr267a, htr268c, htr289a, htr467a, htr789a]
                  ·
                    linarith only [hlam, hd13b, hd89a, htr013a, htr017a, htr178a, htr789a]
              ·
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc123xy, hc789yx, htr013a, htr017a, htr124a, htr179a, htr247a, htr478a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                    linarith only [hlam, hc123xy, hc7810yx, htr013a, htr017a, htr124a, htr1710a, htr247a, htr478a])
                  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456zy, htr157b, htr179a, htr467a, htr567b, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc123xy, hc789zy, htr013a, htr018a, htr124a, htr189a, htr247a, htr479a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hc456zy, htr157b, htr1710a, htr467a, htr567b, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr4710a, htr567a, htr6710a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                    linarith only [hlam, hc123xy, hc7910zy, htr013a, htr019a, htr124a, htr1910a, htr247a, htr4710a])
                  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd12a, hd89b, htr124a, htr247a, htr478a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd12a, hd910b, htr124a, htr247a, htr479a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc178yz, htr189a, htr789c, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hc178yz, htr189b, htr1910a, htr789a, htr8910a]
                ·
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hc456zy, htr157b, htr178a, htr467a, htr567b, htr678a])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc123xy, hc789xy, htr013a, htr017a, htr124a, htr178a, htr247a, htr479a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc123xy, hc7810xy, htr013a, htr017a, htr124a, htr178a, htr247a, htr4710a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc456zy, htr157b, htr179a, htr467a, htr567b, htr679a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc123xy, hc789yz, htr013a, htr017a, htr124a, htr179a, htr248a, htr489a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hc456zy, htr467c, htr4710a, htr567a, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                    linarith only [hlam, hc456zy, htr157b, htr1710a, htr467a, htr567b, htr6710a])
                  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc123xy, hc7910yz, htr013a, htr017a, htr124a, htr1710a, htr249a, htr4910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd13b, hd89a, htr013a, htr017a, htr178a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd13b, hd910a, htr013a, htr017a, htr179a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hc478zy, htr489a, htr789b, htr7910a, htr8910a]
          ·
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc123xy, hc678xy, htr013a, htr016a, htr124a, htr156b, htr246a, htr468a, htr567a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr156b, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr178a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hd13b, hd79a, htr013a, htr016a, htr156b, htr567a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hd13b, hd67a, htr013a, htr017a, htr179a, htr679a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd13b, hd67a, htr013a, htr016c, htr068a, htr567a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc467zy, htr478a, htr567a, htr568a, htr678c])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd12a, hd89b, htr124a, htr247a, htr478a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd67a, hd78b, htr567a, htr568a, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc678xy, htr158b, htr189a, htr567a, htr568b, htr689a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc123xy, hc789zy, htr013a, htr018a, htr124a, htr189a, htr247a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc467zy, htr056b, htr069a, htr479a, htr567a, htr679c])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc8910xy, htr068a, htr069a, htr6810a, htr689b])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc678xy, htr158b, htr1810a, htr567a, htr568b, htr6810a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc123xy, hc8910yz, htr013a, htr018a, htr124a, htr1810a, htr249a, htr4910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd46b, hd910a, htr068a, htr069a, htr468a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc137yx, hc489zy, htr013a, htr018a, htr179a, htr189a, htr4910a, htr7910a]
              ·
                linarith only [hlam, hc467zy, htr479a, htr679b, htr6910a, htr7910a]
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc123xy, hc678yz, htr013a, htr016a, htr124a, htr156b, htr247a, htr478a, htr568a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd13b, hd89a, htr013a, htr016a, htr156b, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd13b, hd810a, htr013a, htr016a, htr156b, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc467zy, htr478a, htr678b, htr689a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc137yx, hc468zy, htr013a, htr016a, htr156b, htr178a, htr489a, htr568a, htr789a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc123xy, hc689yz, htr013a, htr016a, htr124a, htr169a, htr248a, htr489a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc467zy, htr478a, htr678b, htr6810a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hc137yx, hc468zy, htr013a, htr016a, htr156b, htr178a, htr4810a, htr568a, htr7810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc123xy, hc8910zy, htr013a, htr019a, htr124a, htr1910a, htr248a, htr4810a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc679xy, htr156b, htr169b, htr1910a, htr567a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd910b, htr124a, htr248a, htr489a, htr8910a]
              ·
                linarith only [hlam, hd67a, hd89b, htr156b, htr169a, htr567a, htr6910a, htr8910a]
        ·
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc134yx, hc467zy, htr013a, htr016a, htr1410a, htr167a, htr2410a, htr247a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc136yx, htr013a, htr016c, htr067a, htr167a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc134yx, hc478zy, htr013a, htr017a, htr1410a, htr178a, htr2410a, htr248a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
            linarith only [hlam, htr2410c, htr246b, htr2610b])
          obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd14a, hd67b, htr1410a, htr2410a, htr246a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, htr246c, htr2610a, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
            linarith only [hlam, hc046yz, htr0610a, htr2410a, htr246a, htr4610b])
          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0610c, htr067b, htr0710b])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
            linarith only [hlam, hc137yx, htr013a, htr017c, htr0710a, htr1710a])
          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc134yx, hc7810yx, htr013a, htr017a, htr1410a, htr1710a, htr2410a, htr247b, htr278a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hc146yz, htr167a, htr247c, htr278a, htr467c, htr678a]
          ·
            linarith only [hlam, hc146yz, htr167b, htr178a, htr467a, htr678a]
      ·
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc134yx, hc467zy, htr013a, htr016a, htr149a, htr167a, htr247a, htr249a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc136yx, htr013a, htr016c, htr067a, htr167a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc134yx, hc478zy, htr013a, htr017a, htr149a, htr178a, htr248a, htr249a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, htr246b, htr249c, htr269b])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd14a, hd67b, htr149a, htr246a, htr249a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, htr246c, htr269a, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, hc046yz, htr069a, htr246a, htr249a, htr469b])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr067b, htr069c, htr079b])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc137yx, htr013a, htr017c, htr079a, htr179a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc134yx, hc789yx, htr013a, htr017a, htr149a, htr179a, htr247b, htr249a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hc146yz, htr167a, htr247c, htr278a, htr467c, htr678a]
        ·
          linarith only [hlam, hc146yz, htr167b, htr178a, htr467a, htr678a]
    ·
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc134yx, hc467zy, htr013a, htr016a, htr148a, htr167a, htr247a, htr248a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc136yx, htr013a, htr016c, htr067a, htr167a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr246b, htr248c, htr268b])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd14a, hd67b, htr148a, htr246a, htr248a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc468yx, htr246b, htr248a, htr267a, htr467a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, htr246c, htr268a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc046yz, htr068a, htr246a, htr248a, htr468b])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr067b, htr068c, htr078b])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc137yx, htr013a, htr017c, htr078a, htr178a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hc689xy, htr067a, htr068a, htr267a, htr269a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hc134yx, hc789xy, htr013a, htr017a, htr148a, htr178a, htr247b, htr248a, htr279a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hc134yx, hc7810xy, htr013a, htr017a, htr148a, htr178a, htr247b, htr248a, htr2710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, htr246c, htr269a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc146yz, htr167a, htr247c, htr279a, htr467c, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc146yz, htr167b, htr179a, htr467a, htr679a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr249a, htr249b, htr249c, _, _⟩
        linarith only [hlam, hc134yx, hc479zy, htr013a, htr017a, htr148a, htr179a, htr248a, htr249a])
      obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc046yz, htr069a, htr246a, htr249a, htr469b])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        linarith only [hlam, hc146yz, htr167a, htr247c, htr2710a, htr467c, htr6710a])
      obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
      have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
        linarith only [hlam, hc146yz, htr167b, htr1710a, htr467a, htr6710a])
      obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd46b, hd89a, htr067a, htr068a, htr467a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd45b, hd68a, htr245a, htr248a, htr489a, htr689a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd46b, hd910a, htr067a, htr069a, htr467a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd45b, hd69a, htr245a, htr249a, htr4910a, htr6910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc134yx, hc7910yz, htr013a, htr017a, htr148a, htr1710a, htr489a, htr8910a]
      ·
        linarith only [hlam, hc134yx, hc789yz, htr013a, htr017a, htr149a, htr179a, htr4910a, htr8910a]
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, htr246b, htr247c, htr267b])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, htr246c, htr267a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc146yz, htr167a, htr246a, htr247a, htr467b])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc134yx, hc678xy, htr013a, htr016a, htr147a, htr167a, htr246b, htr247a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hc134yx, hc679xy, htr013a, htr016a, htr147a, htr167a, htr246b, htr247a, htr269a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, htr246c, htr268a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, htr246c, htr269a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd13b, hd78a, htr013a, htr016a, htr167a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr478a, htr678a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd13b, hd79a, htr013a, htr016a, htr167a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd45b, hd67a, htr245a, htr247a, htr479a, htr679a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    rcases m.htr 5 6 8 (by decide) (by decide) with
      ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
    ·
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc134yx, hc456zy, htr013a, htr016c, htr068a, htr147a, htr246a, htr247a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc456zy, htr246a, htr248a, htr468b, htr568a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd14a, hd89b, htr147a, htr247a, htr248a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hd14a, hd810b, htr147a, htr247a, htr248a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc256zy, htr158b, htr189a, htr268a, htr568b, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr249a, htr249b, htr249c, _, _⟩
        linarith only [hlam, hc134yx, hc489zy, htr013a, htr018a, htr147a, htr189a, htr247a, htr249a])
      obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc046yz, htr069a, htr246a, htr249a, htr469b])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hc456zy, htr468c, htr4810a, htr568a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hc256zy, htr158b, htr1810a, htr268a, htr568b, htr6810a])
      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd26b, hd910a, htr068a, htr069a, htr268a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd45b, hd69a, htr245a, htr249a, htr4910a, htr6910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      rcases m.htr 7 9 10 (by decide) (by decide) with
        ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      ·
        linarith only [hlam, hc134yx, hc8910yz, htr013a, htr018a, htr147a, htr1810a, htr479a, htr7910a]
      ·
        linarith only [hlam, hc134yx, hc789zy, htr013a, htr018a, htr149a, htr189a, htr4910a, htr7910a]
    ·
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc134yx, hc468zy, htr013a, htr016a, htr147a, htr156b, htr247a, htr248a, htr568a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd13b, hd89a, htr013a, htr016a, htr156b, htr568a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd45b, hd68a, htr245a, htr248a, htr489a, htr689a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hd13b, hd810a, htr013a, htr016a, htr156b, htr568a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hd45b, hd68a, htr245a, htr248a, htr4810a, htr6810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc134yx, hc678yz, htr013a, htr016a, htr148a, htr156b, htr489a, htr568a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc134yx, hc689yz, htr013a, htr016a, htr147a, htr169a, htr478a, htr789a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr249a, htr249b, htr249c, _, _⟩
        linarith only [hlam, hc146yz, htr169a, htr246a, htr249a, htr469b])
      obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd14a, hd910b, htr147a, htr247a, htr249a, htr4910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd49b, hd67a, htr167a, htr169a, htr4910a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
        linarith only [hlam, hc679xy, htr167a, htr169b, htr1910a, htr6910a])
      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
      rcases m.htr 7 8 10 (by decide) (by decide) with
        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
      ·
        linarith only [hlam, hc134yx, hc8910zy, htr013a, htr019a, htr147a, htr1910a, htr478a, htr7810a]
      ·
        linarith only [hlam, hc134yx, hc678yz, htr013a, htr016a, htr148a, htr156b, htr4810a, htr568a, htr7810a]

theorem shard_348 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 1 9 + lam ≤ m.d 0 1)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr147a : m.d 1 4 + lam ≤ m.d 4 7)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr149a : m.d 1 4 + lam ≤ m.d 4 9)
    (htr1410a : m.d 1 4 + lam ≤ m.d 4 10)
    (htr156b : m.d 5 6 < m.d 1 6)
    (htr157b : m.d 5 7 < m.d 1 7)
    (htr158b : m.d 5 8 < m.d 1 8)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr246c : m.d 2 6 < m.d 4 6)
    : False :=
  proof_shard_348 m htr013a htr016a htr016c htr017a htr017c htr018a htr018c htr019a htr026c htr056b htr124a htr126a htr127a htr128a htr147a htr148a htr149a htr1410a htr156b htr157b htr158b htr245a htr246a htr246b htr246c

#print axioms shard_348
end Jsp404.NoSatElevenDBMTerminal
