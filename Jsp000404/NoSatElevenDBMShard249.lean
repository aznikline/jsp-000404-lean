import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_249 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr037b : m.d 3 7 < m.d 0 7)
    (htr038b : m.d 3 8 < m.d 0 8)
    (htr039b : m.d 3 9 < m.d 0 9)
    (htr056c : m.d 0 6 < m.d 5 6)
    (htr057c : m.d 0 7 < m.d 5 7)
    (htr058c : m.d 0 8 < m.d 5 8)
    (htr059c : m.d 0 9 < m.d 5 9)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr138c : m.d 1 8 < m.d 1 3)
    (htr139a : m.d 3 9 + lam ≤ m.d 1 3)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr157c : m.d 1 7 < m.d 5 7)
    (htr158c : m.d 1 8 < m.d 5 8)
    (htr159c : m.d 1 9 < m.d 5 9)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
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
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc148xy, hc148yx, hc148yz, hc148zy⟩ := endpoint_caps m 1 4 8 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc389xy, hc389yx, hc389yz, hc389zy⟩ := endpoint_caps m 3 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    rcases m.htr 2 3 8 (by decide) (by decide) with
      ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
    ·
      rcases m.htr 2 3 9 (by decide) (by decide) with
        ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
      ·
        rcases m.htr 2 3 10 (by decide) (by decide) with
          ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
        ·
          rcases m.htr 3 6 7 (by decide) (by decide) with
            ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
          ·
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc123zy, htr136c, htr167a, htr236a, htr367a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr367a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd34a, hd78b, htr234a, htr236a, htr367a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr378a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hd34a, hd79b, htr234a, htr236a, htr367a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr379a, htr679a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd14a, hd89b, htr014a, htr016a, htr156c, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hd34a, hd68b, htr234a, htr238a, htr389a, htr689a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd14a, hd810b, htr014a, htr016a, htr156c, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                linarith only [hlam, hd34a, hd68b, htr234a, htr238a, htr3810a, htr6810a])
              obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc134yx, hc678zy, htr014a, htr016a, htr138a, htr156c, htr389a, htr568a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc134yx, hc689zy, htr014a, htr016a, htr137a, htr169a, htr378a, htr789a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc134yx, hc678zy, htr014a, htr016a, htr138a, htr156c, htr3810a, htr568a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc134yx, hc8910yz, htr014a, htr019a, htr137a, htr1910a, htr378a, htr7810a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc679yx, htr167a, htr169c, htr1910a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd67b, hd89a, htr167a, htr169a, htr6910a, htr8910a]
              ·
                linarith only [hlam, hd13b, hd910a, htr137a, htr378a, htr789a, htr8910a]
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd34a, hd67b, htr036b, htr068a, htr234a, htr236a, htr567a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hd34a, hd67b, htr234a, htr236b, htr268a, htr567a, htr568a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              rcases m.htr 5 6 9 (by decide) (by decide) with
                ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, htr056c, htr069a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, htr068c, htr069b, htr089c])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr038b, htr089a, htr158c, htr189a, htr234a, htr238a, htr567a, htr568c])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                  linarith only [hlam, htr026b, htr056c, htr269a, htr569a])
                obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc124yx, hc8910yx, htr014a, htr018a, htr126a, htr189a, htr268a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, hc678yx, htr058c, htr0810a, htr567a, htr568c, htr6810a])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr038b, htr0810a, htr158c, htr1810a, htr234a, htr238a, htr567a, htr568c])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd14a, hd910b, htr014a, htr016a, htr156c, htr569a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                  linarith only [hlam, hc689xy, htr268a, htr269b, htr2910a, htr6910a])
                obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc124yx, hc679zy, htr014a, htr016a, htr129a, htr156c, htr2910a, htr569a, htr7910a]
                ·
                  linarith only [hlam, hc134yx, hc8910zy, htr014a, htr018a, htr137a, htr1810a, htr379a, htr7910a]
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr036b, htr069a, htr234a, htr236a, htr567a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                  linarith only [hlam, hc678yx, htr268a, htr269a, htr567a, htr569a])
                obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                rcases m.htr 5 6 10 (by decide) (by decide) with
                  ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                ·
                  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                    linarith only [hlam, htr056c, htr0610a, htr5610a])
                  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                    linarith only [hlam, htr0610b, htr068c, htr0810c])
                  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                    linarith only [hlam, htr0610b, htr069c, htr0910c])
                  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                  have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                    linarith only [hlam, hd34a, hd67b, htr038b, htr0810a, htr158c, htr1810a, htr234a, htr238a, htr567a, htr568c])
                  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc124yx, hc8910xy, htr014a, htr018a, htr126a, htr1810a, htr268a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, hc678yx, htr058c, htr089a, htr567a, htr568c, htr689a])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd34a, hd910b, htr038b, htr089a, htr234a, htr238a, htr8910a]
                  ·
                    linarith only [hlam, hd34a, hd89b, htr039b, htr0910a, htr234a, htr239a, htr8910a]
                ·
                  rcases m.htr 5 8 9 (by decide) (by decide) with
                    ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
                  ·
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc124yx, hc8910yx, htr014a, htr018a, htr126a, htr158c, htr268a, htr589a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc678yx, htr058c, htr0810a, htr567a, htr568c, htr6810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hd34a, hd67b, htr038b, htr0810a, htr158c, htr1810a, htr234a, htr238a, htr567a, htr568c])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc124yx, hc8910zy, htr014a, htr018a, htr126a, htr1810a, htr269a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                      linarith only [hlam, hc679yx, htr059c, htr0910a, htr567a, htr569c, htr6910a])
                    obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd14a, hd910b, htr014a, htr018a, htr158c, htr589a, htr8910a]
                    ·
                      linarith only [hlam, hd34a, hd89b, htr039b, htr0910a, htr234a, htr239a, htr8910a]
                  ·
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hc678yx, htr567a, htr568c, htr589a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hc124yx, hc8910xy, htr014a, htr018a, htr126a, htr1810a, htr268a, htr689a])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc678yx, htr158c, htr1810a, htr567a, htr568c, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                      linarith only [hlam, hc124yx, hc8910yz, htr014a, htr019a, htr126a, htr1910a, htr268a, htr6810a])
                    obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc679yx, htr159c, htr1910a, htr567a, htr569c, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd67b, hd89a, htr567a, htr569a, htr6910a, htr8910a]
                    ·
                      linarith only [hlam, hd67b, hd910a, htr567a, htr568a, htr689a, htr8910a]
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, htr036b, htr067a, htr367a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, htr136b, htr167a, htr367a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc123zy, htr136a, htr236b, htr267a, htr367a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            rcases m.htr 3 6 8 (by decide) (by decide) with
              ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hc023zy, htr036c, htr068a, htr236a, htr368a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, htr067c, htr068b, htr078c])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc123zy, htr136c, htr168a, htr236a, htr368a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hd34a, hd68b, htr037b, htr078a, htr167c, htr168a, htr178a, htr234a, htr237a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, htr236c, htr268a, htr368a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc134yx, hc789yx, htr014a, htr017a, htr136a, htr178a, htr367a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hc678xy, htr067c, htr068a, htr079a, htr679a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hd34a, hd68b, htr037b, htr079a, htr167c, htr168a, htr179a, htr234a, htr237a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                linarith only [hlam, hc134yx, hc7810yx, htr014a, htr017a, htr136a, htr178a, htr367a, htr6710a])
              obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, hc678xy, htr067c, htr068a, htr0710a, htr6710a])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hd34a, hd68b, htr037b, htr0710a, htr167c, htr168a, htr1710a, htr234a, htr237a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd34a, hd89b, htr234a, htr236a, htr368a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc678xy, htr267a, htr268b, htr289a, htr689a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd34a, hd910b, htr037b, htr079a, htr234a, htr237a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                linarith only [hlam, hd34a, hd79b, htr234a, htr239a, htr3910a, htr7910a])
              obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc134yx, hc789zy, htr014a, htr017a, htr139a, htr179a, htr3910a, htr8910a]
              ·
                linarith only [hlam, hc124yx, hc7910zy, htr014a, htr017a, htr128a, htr1710a, htr289a, htr8910a]
            ·
              rcases m.htr 3 7 8 (by decide) (by decide) with
                ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
              ·
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc123zy, htr137c, htr178a, htr237a, htr378a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, htr237c, htr278a, htr378a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd34a, hd89b, htr234a, htr237a, htr378a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hd34a, hd78b, htr234a, htr238a, htr389a, htr789a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc134yx, hc678yz, htr014a, htr017a, htr138a, htr178a, htr389a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc134yx, hc789zy, htr014a, htr017a, htr136a, htr179a, htr368a, htr689a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc134yx, hc8910xy, htr014a, htr018a, htr136a, htr1810a, htr368a, htr689a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, hd34a, hd78b, htr178a, htr179a, htr234a, htr237b, htr279a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hc148xy, hc789yx, htr014a, htr017a, htr178a, htr1810a, htr278b, htr279a, htr2810a])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc124yx, hc678yz, htr014a, htr017a, htr128a, htr178a, htr2810a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                  linarith only [hlam, hc134yx, hc8910yz, htr014a, htr019a, htr136a, htr1910a, htr368a, htr6810a])
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
                  linarith only [hlam, hd13b, hd910a, htr136a, htr368a, htr689a, htr8910a]
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr037b, htr078a, htr378a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, htr137b, htr178a, htr378a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc123zy, htr137a, htr237b, htr278a, htr378a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                    linarith only [hlam, hc679xy, htr267c, htr269a, htr278a, htr678a])
                  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd13b, hd79a, htr137a, htr378a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  rcases m.htr 5 7 9 (by decide) (by decide) with
                    ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, htr057c, htr079a, htr579a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr078c, htr079b, htr089c])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hd34a, hd79b, htr038b, htr089a, htr157c, htr178c, htr189a, htr234a, htr238a, htr579a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, htr127b, htr157c, htr279a, htr579a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      linarith only [hlam, hc134yx, hc8910yx, htr014a, htr018a, htr137a, htr189a, htr378a, htr7810a])
                    obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc067zy, htr078c, htr0810a, htr678a, htr7810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                      linarith only [hlam, hd34a, hd79b, htr038b, htr0810a, htr157c, htr178c, htr1810a, htr234a, htr238a, htr579a])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc124yx, hc8910zy, htr014a, htr018a, htr126a, htr1810a, htr269a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                      linarith only [hlam, hc124yx, hc679yz, htr014a, htr017a, htr129a, htr157c, htr2910a, htr579a, htr6910a])
                    obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd34a, hd910b, htr038b, htr089a, htr234a, htr238a, htr8910a]
                    ·
                      linarith only [hlam, hd67a, hd89b, htr278a, htr279b, htr2910a, htr678a, htr8910a]
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, hc567zy, htr037b, htr079a, htr378a, htr579a, htr678a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, hc567zy, htr278a, htr279a, htr579a, htr678a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    rcases m.htr 5 7 10 (by decide) (by decide) with
                      ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    ·
                      have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                        linarith only [hlam, htr057c, htr0710a, htr5710a])
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
                        linarith only [hlam, hd34a, hd710b, htr038b, htr0810a, htr157c, htr178c, htr1810a, htr234a, htr238a, htr5710a])
                      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hc134yx, hc8910xy, htr014a, htr018a, htr137a, htr1810a, htr378a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, hc067zy, htr078c, htr089a, htr678a, htr789a])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd34a, hd910b, htr038b, htr089a, htr234a, htr238a, htr8910a]
                      ·
                        linarith only [hlam, hd34a, hd89b, htr039b, htr0910a, htr234a, htr239a, htr8910a]
                    ·
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, hc067zy, htr078c, htr089a, htr678a, htr789a])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc167zy, htr178c, htr189a, htr678a, htr789a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc134yx, hc8910yx, htr014a, htr018a, htr137a, htr189a, htr378a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, hc067zy, htr078c, htr0810a, htr678a, htr7810a])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                          linarith only [hlam, hd34a, hd89b, htr038b, htr0810a, htr1810a, htr189a, htr234a, htr238a])
                        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hc124yx, hc8910zy, htr014a, htr018a, htr126a, htr1810a, htr269a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                          linarith only [hlam, hc124yx, hc689yz, htr014a, htr018a, htr129a, htr189a, htr2910a, htr6910a])
                        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                          linarith only [hlam, hc567zy, htr059c, htr0910a, htr279b, htr2910a, htr579c, htr679a])
                        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd34a, hd910b, htr038b, htr089a, htr234a, htr238a, htr8910a]
                        ·
                          linarith only [hlam, hd34a, hd89b, htr039b, htr0910a, htr234a, htr239a, htr8910a]
                      ·
                        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                          linarith only [hlam, hc134yx, hc8910xy, htr014a, htr018a, htr137a, htr1810a, htr378a, htr789a])
                        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                          linarith only [hlam, hc167zy, htr178c, htr1810a, htr278b, htr2810a, htr678a])
                        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hd13b, hd68a, htr137a, htr378a, htr689a, htr789a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                          linarith only [hlam, hd12b, hd89a, htr128a, htr2810a, htr6810a, htr689a])
                        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                          linarith only [hlam, hc134yx, hc8910yz, htr014a, htr019a, htr136a, htr1910a, htr368a, htr6810a])
                        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hc567zy, htr159c, htr1910a, htr579c, htr679a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd12b, hd89a, htr127a, htr279a, htr7910a, htr8910a]
                        ·
                          linarith only [hlam, hd13b, hd910a, htr137a, htr378a, htr789a, htr8910a]
                ·
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc134yx, hc789xy, htr014a, htr017a, htr136a, htr179a, htr367a, htr678a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                    linarith only [hlam, hc134yx, hc7810xy, htr014a, htr017a, htr136a, htr1710a, htr367a, htr678a])
                  obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                    linarith only [hlam, hc123zy, htr137c, htr179a, htr237a, htr379a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                    linarith only [hlam, hc123zy, htr137c, htr1710a, htr237a, htr3710a])
                  obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd13b, hd78a, htr137a, htr379a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc134yx, hc789yz, htr014a, htr018a, htr136a, htr189a, htr367a, htr679a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                    linarith only [hlam, hc123zy, htr138c, htr189a, htr238a, htr389a])
                  obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd13b, hd78a, htr137a, htr3710a, htr6710a, htr678a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                    linarith only [hlam, hc134yx, hc7910yz, htr014a, htr019a, htr136a, htr1910a, htr367a, htr6710a])
                  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd13b, hd89a, htr136a, htr367a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd13b, hd910a, htr136a, htr367a, htr679a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc178zy, htr189c, htr1910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hd13b, hd79a, htr138a, htr389a, htr7910a, htr8910a]
        ·
          have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
            linarith only [hlam, htr2310c, htr236b, htr2610b])
          obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
          have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
            linarith only [hlam, htr2310c, htr237b, htr2710b])
          obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
          have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
            linarith only [hlam, htr2310c, htr238b, htr2810b])
          obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr236c, htr2610a, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc6710yx, htr2310a, htr236a, htr3610b, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr237c, htr2710a, htr3710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc7810yx, htr2310a, htr237a, htr3710b, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, htr238c, htr2810a, htr3810a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hd13b, hd67a, htr136a, htr2310a, htr236a, htr3710b, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd13b, hd710a, htr137a, htr378a, htr6710a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd13b, hd78a, htr136a, htr2310a, htr236a, htr3810b, htr7810a]
          ·
            linarith only [hlam, hd13b, hd810a, htr136a, htr367a, htr678a, htr7810a]
      ·
        have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr269a, htr269b, htr269c, _, _⟩
          linarith only [hlam, htr236b, htr239c, htr269b])
        obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, htr237b, htr239c, htr279b])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, htr238b, htr239c, htr289b])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr236c, htr269a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc679yx, htr236a, htr239a, htr367a, htr369b])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr237c, htr279a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc789yx, htr237a, htr239a, htr378a, htr379b])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, htr238c, htr289a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd13b, hd67a, htr136a, htr236a, htr239a, htr379b, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd13b, hd79a, htr137a, htr378a, htr678a, htr679a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd13b, hd78a, htr136a, htr236a, htr239a, htr389b, htr789a]
        ·
          linarith only [hlam, hd13b, hd89a, htr136a, htr367a, htr678a, htr789a]
    ·
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, htr236b, htr238c, htr268b])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, htr237b, htr238c, htr278b])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr236c, htr268a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc678yx, htr236a, htr238a, htr367a, htr368b])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr237c, htr278a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hc789xy, htr237a, htr238a, htr378b, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
        linarith only [hlam, hc7810xy, htr237a, htr238a, htr3710a, htr378b])
      obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd13b, hd89a, htr136a, htr236a, htr238a, htr389a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd13b, hd67a, htr136a, htr236a, htr238a, htr378b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr137a, htr379a, htr678a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc134yx, hc789yz, htr014a, htr018a, htr136a, htr189a, htr367a, htr679a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr239a, htr239b, htr239c, _, _⟩
        linarith only [hlam, hc138zy, htr189a, htr238a, htr239a, htr389c])
      obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
      have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
        linarith only [hlam, hd13b, hd910a, htr136a, htr236a, htr239a, htr3910a])
      obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
      have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr137a, htr3710a, htr6710a, htr678a])
      obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
        linarith only [hlam, hc134yx, hc7910yz, htr014a, htr019a, htr136a, htr1910a, htr367a, htr6710a])
      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc138zy, htr189c, htr1910a, htr389a, htr8910a]
      ·
        linarith only [hlam, hc138zy, htr189a, htr389b, htr3910a, htr8910a]
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, htr236b, htr237c, htr267b])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr236c, htr267a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc678xy, htr236a, htr237a, htr367b, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hc679xy, htr236a, htr237a, htr367b, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd13b, hd78a, htr136a, htr236a, htr237a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd13b, hd79a, htr136a, htr236a, htr237a, htr379a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    rcases m.htr 5 7 8 (by decide) (by decide) with
      ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
    ·
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc134yx, hc378yz, htr014a, htr017a, htr136a, htr157c, htr236a, htr238a, htr578a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd14a, hd89b, htr014a, htr017a, htr157c, htr578a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd34a, hd78b, htr234a, htr238a, htr389a, htr789a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc134yx, hc678yz, htr014a, htr017a, htr138a, htr157c, htr389a, htr578a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc134yx, hc789zy, htr014a, htr017a, htr136a, htr179a, htr368a, htr689a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hc134yx, hc8910xy, htr014a, htr018a, htr136a, htr1810a, htr368a, htr689a])
      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
      have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr239a, htr239b, htr239c, _, _⟩
        linarith only [hlam, hc137zy, htr179a, htr237a, htr239a, htr379c])
      obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
      have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
        linarith only [hlam, hc123zy, htr138c, htr1810a, htr238a, htr3810a])
      obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
      have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
        linarith only [hlam, hd13b, hd910a, htr136a, htr236a, htr239a, htr3910a])
      obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hc134yx, hc678yz, htr014a, htr017a, htr138a, htr157c, htr3810a, htr578a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
        linarith only [hlam, hc134yx, hc8910yz, htr014a, htr019a, htr136a, htr1910a, htr368a, htr6810a])
      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
      rcases m.htr 7 9 10 (by decide) (by decide) with
        ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      ·
        linarith only [hlam, hc137zy, htr179c, htr1910a, htr379a, htr7910a]
      ·
        linarith only [hlam, hc137zy, htr179a, htr379b, htr3910a, htr7910a]
    ·
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc357yz, htr237a, htr238a, htr378c, htr578a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd13b, hd89a, htr136a, htr236a, htr238a, htr389a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
        linarith only [hlam, hd13b, hd810a, htr136a, htr236a, htr238a, htr3810a])
      obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc357yz, htr378b, htr389a, htr578a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc357yz, htr158c, htr189a, htr378a, htr578c, htr789a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr239a, htr239b, htr239c, _, _⟩
        linarith only [hlam, hc134yx, hc389yz, htr014a, htr018a, htr136a, htr189a, htr236a, htr239a])
      obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        linarith only [hlam, hc357yz, htr378b, htr3810a, htr578a, htr7810a])
      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hc357yz, htr158c, htr1810a, htr378a, htr578c, htr7810a])
      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc134yx, hc8910zy, htr014a, htr018a, htr136a, htr1810a, htr369a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
        linarith only [hlam, hc134yx, hc689yz, htr014a, htr018a, htr139a, htr189a, htr3910a, htr6910a])
      obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hd14a, hd910b, htr014a, htr018a, htr189a, htr8910a]
      ·
        linarith only [hlam, hd34a, hd89b, htr234a, htr239a, htr3910a, htr8910a]

theorem shard_249 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr037b : m.d 3 7 < m.d 0 7)
    (htr038b : m.d 3 8 < m.d 0 8)
    (htr039b : m.d 3 9 < m.d 0 9)
    (htr056c : m.d 0 6 < m.d 5 6)
    (htr057c : m.d 0 7 < m.d 5 7)
    (htr058c : m.d 0 8 < m.d 5 8)
    (htr059c : m.d 0 9 < m.d 5 9)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr138c : m.d 1 8 < m.d 1 3)
    (htr139a : m.d 3 9 + lam ≤ m.d 1 3)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr157c : m.d 1 7 < m.d 5 7)
    (htr158c : m.d 1 8 < m.d 5 8)
    (htr159c : m.d 1 9 < m.d 5 9)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    : False :=
  proof_shard_249 m htr014a htr016a htr017a htr018a htr019a htr026b htr036b htr036c htr037b htr038b htr039b htr056c htr057c htr058c htr059c htr126a htr127a htr127b htr128a htr129a htr136a htr136b htr136c htr137a htr137b htr137c htr138a htr138c htr139a htr156c htr157c htr158c htr159c htr234a htr236a htr236b htr236c

#print axioms shard_249
end Jsp404.NoSatElevenDBMTerminal
