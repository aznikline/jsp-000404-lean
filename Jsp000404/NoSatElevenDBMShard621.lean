import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_621 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr247b : m.d 2 4 < m.d 2 7)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr349c : m.d 3 9 < m.d 4 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd06a, hd06braw⟩ := m.hrange 0 6 (by decide)
  have hd06b : m.d 0 6 < 4*lam := by
    linarith only [hd06braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd49a, hd49braw⟩ := m.hrange 4 9 (by decide)
  have hd49b : m.d 4 9 < 4*lam := by
    linarith only [hd49braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
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
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc037xy, hc037yx, hc037yz, hc037zy⟩ := endpoint_caps m 0 3 7 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc349xy, hc349yx, hc349yz, hc349zy⟩ := endpoint_caps m 3 4 9 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc379xy, hc379yx, hc379yz, hc379zy⟩ := endpoint_caps m 3 7 9 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc5710xy, hc5710yx, hc5710yz, hc5710zy⟩ := endpoint_caps m 5 7 10 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc034zy, htr045a, htr234a, htr235a, htr345c])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced135 := (m.htr 1 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr135a, htr135b, htr135c, _, _⟩
    linarith only [hlam, hd01b, hd34a, htr013a, htr135a, htr234a, htr235a])
  obtain ⟨htr135a, htr135b, htr135c, _, _⟩ := hforced135
  rcases m.htr 2 3 6 (by decide) (by decide) with
    ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
  ·
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, hc345xy, htr135a, htr136a, htr234a, htr236a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    rcases m.htr 2 3 7 (by decide) (by decide) with
      ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
    ·
      rcases m.htr 0 3 5 (by decide) (by decide) with
        ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
      ·
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc345xy, htr035a, htr036a, htr234a, htr236a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        rcases m.htr 2 3 8 (by decide) (by decide) with
          ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
        ·
          rcases m.htr 2 3 9 (by decide) (by decide) with
            ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
          ·
            rcases m.htr 2 3 10 (by decide) (by decide) with
              ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
            ·
              rcases m.htr 2 5 6 (by decide) (by decide) with
                ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
              ·
                have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                  linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
                obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr234a, htr235a, htr356a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr367a, htr567a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, hc346xy, htr234a, htr236b, htr267a, htr367a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd34a, hd68b, htr234a, htr235a, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr368a, htr568a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hc346xy, htr234a, htr236b, htr268a, htr368a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc347xy, htr234a, htr237b, htr278a, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd01b, hd89a, htr012a, htr126a, htr268a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hd01b, hd68a, htr012a, htr128a, htr289a, htr689a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc348xy, htr234a, htr238b, htr289a, htr389a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd34a, hd89b, htr234a, htr237a, htr378a, htr789a]
                ·
                  linarith only [hlam, hd34a, hd78b, htr234a, htr238a, htr389a, htr789a]
              ·
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd01b, hd67a, htr012a, htr125a, htr256a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr267a, htr567a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc346xy, htr234a, htr236b, htr267a, htr367a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd01b, hd68a, htr012a, htr125a, htr256a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr268a, htr568a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc346xy, htr234a, htr236b, htr268a, htr368a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd34a, hd78b, htr234a, htr236a, htr367a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr378a, htr678a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc347xy, htr234a, htr237b, htr278a, htr378a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd34a, hd89b, htr234a, htr236a, htr368a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hd34a, hd68b, htr234a, htr238a, htr389a, htr689a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hc348xy, htr234a, htr238b, htr289a, htr389a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
                ·
                  linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
            ·
              have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
                linarith only [hlam, htr013b, htr0310a, htr123b, htr2310a])
              obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
              have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                linarith only [hlam, htr0310c, htr035b, htr0510b])
              obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                linarith only [hlam, htr0310c, htr036b, htr0610b])
              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
              have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                linarith only [hlam, hc346xy, htr036c, htr0610a, htr234a, htr236b, htr2610a])
              obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
              have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                linarith only [hlam, htr035c, htr0510a, htr3510a])
              obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hc5610yx, htr123b, htr135a, htr2310a, htr3510b, htr356a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr2610a, htr5610a]
              ·
                linarith only [hlam, hd01b, hd610a, htr012a, htr125a, htr256a, htr5610a]
          ·
            have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr039a, htr039b, htr039c, _, _⟩
              linarith only [hlam, htr013b, htr039a, htr123b, htr239a])
            obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
            have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr059a, htr059b, htr059c, _, _⟩
              linarith only [hlam, htr035b, htr039c, htr059b])
            obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr036b, htr039c, htr069b])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr269a, htr269b, htr269c, _, _⟩
              linarith only [hlam, hc346xy, htr036c, htr069a, htr234a, htr236b, htr269a])
            obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
            have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr359a, htr359b, htr359c, _, _⟩
              linarith only [hlam, htr035c, htr059a, htr359a])
            obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc569yx, htr123b, htr135a, htr239a, htr356a, htr359b])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            rcases m.htr 5 6 9 (by decide) (by decide) with
              ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
            ·
              linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr269a, htr569a]
            ·
              linarith only [hlam, hd01b, hd69a, htr012a, htr125a, htr256a, htr569a]
        ·
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr013b, htr038a, htr123b, htr238a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr035b, htr038c, htr058b])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr036b, htr038c, htr068b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hc346xy, htr036c, htr068a, htr234a, htr236b, htr268a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr035c, htr058a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc568yx, htr123b, htr135a, htr238a, htr356a, htr358b])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          rcases m.htr 5 6 8 (by decide) (by decide) with
            ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
          ·
            linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr268a, htr568a]
          ·
            linarith only [hlam, hd01b, hd68a, htr012a, htr125a, htr256a, htr568a]
      ·
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hc346xy, htr035a, htr036a, htr234a, htr235a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        rcases m.htr 2 3 8 (by decide) (by decide) with
          ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
        ·
          rcases m.htr 2 3 9 (by decide) (by decide) with
            ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
          ·
            rcases m.htr 2 3 10 (by decide) (by decide) with
              ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
            ·
              rcases m.htr 3 5 6 (by decide) (by decide) with
                ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
              ·
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr234a, htr235a, htr356a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr367a, htr567a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, hc346xy, htr234a, htr236b, htr267a, htr367a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd34a, hd68b, htr234a, htr235a, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr368a, htr568a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hc346xy, htr234a, htr236b, htr268a, htr368a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd01b, hd78a, htr012a, htr126a, htr267a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hd01b, hd67a, htr012a, htr127a, htr278a, htr678a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc347xy, htr234a, htr237b, htr278a, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd01b, hd89a, htr012a, htr126a, htr268a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hd01b, hd68a, htr012a, htr128a, htr289a, htr689a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc348xy, htr234a, htr238b, htr289a, htr389a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd34a, hd89b, htr234a, htr237a, htr378a, htr789a]
                ·
                  linarith only [hlam, hd34a, hd78b, htr234a, htr238a, htr389a, htr789a]
              ·
                have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                  linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
                obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd01b, hd67a, htr012a, htr125a, htr256a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr267a, htr567a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc346xy, htr234a, htr236b, htr267a, htr367a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, hd06b, hd34a, htr067a, htr234a, htr236a, htr367a])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd01b, hd68a, htr012a, htr125a, htr256a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr268a, htr568a])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr067a, htr068a, htr234a, htr236b, htr268a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd34a, hd78b, htr234a, htr236a, htr367a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr378a, htr678a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc347xy, htr234a, htr237b, htr278a, htr378a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd34a, hd89b, htr036b, htr068a, htr234a, htr236a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hd34a, hd68b, htr234a, htr238a, htr389a, htr689a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hc348xy, htr234a, htr238b, htr289a, htr389a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd01b, hd78a, htr012a, htr128a, htr289a, htr789a]
                ·
                  linarith only [hlam, hd01b, hd89a, htr012a, htr127a, htr278a, htr789a]
            ·
              have hforced1310 := (m.htr 1 3 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1310a, htr1310b, htr1310c, _, _⟩
                linarith only [hlam, htr123b, htr1310a, htr2310a])
              obtain ⟨htr1310a, htr1310b, htr1310c, _, _⟩ := hforced1310
              have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
                linarith only [hlam, htr1310c, htr135b, htr1510b])
              obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
              have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                linarith only [hlam, htr1310c, htr136b, htr1610b])
              obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
              have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                linarith only [hlam, hd01b, hd34a, htr016a, htr1610a, htr234a, htr236b, htr2610a])
              obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
              have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                linarith only [hlam, htr135c, htr1510a, htr3510a])
              obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hc5610yx, htr123b, htr135a, htr2310a, htr3510b, htr356a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr2610a, htr5610a]
              ·
                linarith only [hlam, hd01b, hd610a, htr012a, htr125a, htr256a, htr5610a]
          ·
            have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr139a, htr139b, htr139c, _, _⟩
              linarith only [hlam, htr123b, htr139a, htr239a])
            obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
            have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr159a, htr159b, htr159c, _, _⟩
              linarith only [hlam, htr135b, htr139c, htr159b])
            obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
            have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr169a, htr169b, htr169c, _, _⟩
              linarith only [hlam, htr136b, htr139c, htr169b])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr269a, htr269b, htr269c, _, _⟩
              linarith only [hlam, hd01b, hd34a, htr016a, htr169a, htr234a, htr236b, htr269a])
            obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
            have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr359a, htr359b, htr359c, _, _⟩
              linarith only [hlam, htr135c, htr159a, htr359a])
            obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc569yx, htr123b, htr135a, htr239a, htr356a, htr359b])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            rcases m.htr 5 6 9 (by decide) (by decide) with
              ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
            ·
              linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr269a, htr569a]
            ·
              linarith only [hlam, hd01b, hd69a, htr012a, htr125a, htr256a, htr569a]
        ·
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, htr123b, htr138a, htr238a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, htr135b, htr138c, htr158b])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, htr136b, htr138c, htr168b])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
            linarith only [hlam, hd01b, hd34a, htr016a, htr168a, htr234a, htr236b, htr268a])
          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr135c, htr158a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc568yx, htr123b, htr135a, htr238a, htr356a, htr358b])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          rcases m.htr 5 6 8 (by decide) (by decide) with
            ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
          ·
            linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr268a, htr568a]
          ·
            linarith only [hlam, hd01b, hd68a, htr012a, htr125a, htr256a, htr568a]
    ·
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, htr123b, htr137a, htr237a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, htr135b, htr137c, htr157b])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, htr136b, htr137c, htr167b])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hd01b, hd34a, htr016a, htr167a, htr234a, htr236b, htr267a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr135c, htr157a, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hc567yx, htr123b, htr135a, htr237a, htr356a, htr357b])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr256a, htr256b, htr256c, _, _⟩
        linarith only [hlam, hc345xy, htr234a, htr235b, htr256a, htr356a])
      obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        linarith only [hlam, hd01b, hd56a, htr012a, htr126a, htr267a, htr567a]
      ·
        linarith only [hlam, hd01b, hd67a, htr012a, htr125a, htr256a, htr567a]
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr013b, htr036a, htr123b, htr236a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr136a, htr136b, htr136c, _, _⟩
      linarith only [hlam, htr123b, htr136a, htr236a])
    obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, htr135b, htr136c, htr156b])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, htr135c, htr156a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc567xy, htr123b, htr135a, htr236a, htr356b, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr257a, htr257b, htr257c, _, _⟩
      linarith only [hlam, hc345xy, htr234a, htr235b, htr257a, htr357a])
    obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc568xy, htr123b, htr135a, htr236a, htr356b, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
      linarith only [hlam, hc345xy, htr234a, htr235b, htr258a, htr358a])
    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
    have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr359a, htr359b, htr359c, _, _⟩
      linarith only [hlam, hc569xy, htr123b, htr135a, htr236a, htr356b, htr359a])
    obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
    have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr259a, htr259b, htr259c, _, _⟩
      linarith only [hlam, hc345xy, htr234a, htr235b, htr259a, htr359a])
    obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
    have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
      linarith only [hlam, hc5610xy, htr123b, htr135a, htr236a, htr3510a, htr356b])
    obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
    have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
      linarith only [hlam, hc345xy, htr234a, htr235b, htr2510a, htr3510a])
    obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd01b, hd67a, htr012a, htr123a, htr236a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hd01b, hd68a, htr012a, htr123a, htr236a, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hd01b, hd69a, htr012a, htr123a, htr236a, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
      linarith only [hlam, hd01b, hd610a, htr012a, htr123a, htr236a, htr3610a])
    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, htr356b, htr367a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, htr356b, htr368a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr278a, htr578a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd01b, hd79a, htr012a, htr125a, htr257a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
      linarith only [hlam, hd01b, hd710a, htr012a, htr125a, htr257a, htr5710a])
    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
      linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr2710a, htr5710a])
    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hd01b, hd58a, htr012a, htr128a, htr289a, htr589a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
      linarith only [hlam, hd01b, hd810a, htr012a, htr125a, htr258a, htr5810a])
    obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
      linarith only [hlam, hd01b, hd58a, htr012a, htr128a, htr2810a, htr5810a])
    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
      linarith only [hlam, hd01b, hd910a, htr012a, htr125a, htr259a, htr5910a])
    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
    have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
      linarith only [hlam, hd01b, hd59a, htr012a, htr129a, htr2910a, htr5910a])
    obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
    rcases m.htr 2 3 7 (by decide) (by decide) with
      ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
    ·
      have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr137a, htr137b, htr137c, _, _⟩
        linarith only [hlam, hc345xy, htr135a, htr137a, htr234a, htr237a])
      obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hd01b, hd34a, htr017a, htr178a, htr234a, htr237b, htr278a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr137b, htr138c, htr178b])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc347xy, htr234a, htr237b, htr278a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc348xy, htr234a, htr237b, htr278b, htr289a, htr389a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd34a, hd89b, htr234a, htr237a, htr378a, htr789a]
      ·
        linarith only [hlam, hd34a, hd78b, htr123b, htr138a, htr234a, htr389a, htr789a]
    ·
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr013b, htr037a, htr123b, htr237a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
        linarith only [hlam, htr237b, htr2710a, htr3710a])
      obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
      rcases m.htr 0 3 5 (by decide) (by decide) with
        ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
      ·
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc345xy, htr034c, htr035a, htr046a, htr346a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc356yx, htr035a, htr036c, htr067a, htr367a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc356yx, htr035a, htr036c, htr068a, htr368a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc345xy, htr035a, htr037c, htr078a, htr234b, htr247b, htr278a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc014yx, hc578yz, htr012a, htr046a, htr125a, htr258a, htr467a, htr678a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
            linarith only [hlam, hc016yx, hc568yz, htr012a, htr067a, htr125a, htr258a, htr467a, htr468a])
          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hc016yx, hc589yz, htr012a, htr067a, htr125a, htr259a, htr678a, htr789a]
          ·
            linarith only [hlam, hc016yx, hc578yz, htr012a, htr068a, htr125a, htr258a, htr689a, htr789a]
        ·
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
            linarith only [hlam, hc016yx, hc567yz, htr012a, htr068a, htr125a, htr257a, htr467a, htr468a])
          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc014yx, hc589yz, htr012a, htr046a, htr125a, htr259a, htr468a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hc017yx, hc568yz, htr012a, htr078a, htr125a, htr258a, htr689a, htr789a]
          ·
            linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
      ·
        rcases m.htr 2 3 8 (by decide) (by decide) with
          ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
        ·
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc345xy, htr135a, htr138a, htr234a, htr238a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hd01b, hd34a, htr018a, htr189a, htr234a, htr238b, htr289a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr139a, htr139b, htr139c, _, _⟩
            linarith only [hlam, htr138b, htr139c, htr189b])
          obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc348xy, htr234a, htr238b, htr289a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hc349xy, htr234a, htr238b, htr289b, htr2910a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd910b, htr234a, htr238a, htr389a, htr8910a]
          ·
            linarith only [hlam, hd34a, hd89b, htr123b, htr139a, htr234a, htr3910a, htr8910a]
        ·
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, htr238b, htr2810a, htr3810a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          rcases m.htr 2 3 9 (by decide) (by decide) with
            ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
          ·
            have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr049a, htr049b, htr049c, _, _⟩
              linarith only [hlam, hc034zy, htr049a, htr234a, htr239a, htr349c])
            obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
            have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
              linarith only [hlam, hc349xy, htr234a, htr239b, htr2910a, htr3910a])
            obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
            have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr469a, htr469b, htr469c, _, _⟩
              linarith only [hlam, hc346yz, htr236a, htr239a, htr369c, htr469a])
            obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hd34a, hd49b, htr234a, htr239a, htr3910a, htr4910a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr046a, htr046b, htr046c, _, _⟩
              linarith only [hlam, hd34a, hd910b, htr046a, htr049a, htr346a, htr4910a])
            obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
            rcases m.htr 6 9 10 (by decide) (by decide) with
              ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            ·
              linarith only [hlam, hc014yx, hc5910yz, htr012a, htr046a, htr125a, htr2510a, htr469a, htr6910a]
            ·
              linarith only [hlam, hd34a, hd69b, htr234a, htr239a, htr3910a, htr6910a]
          ·
            have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
              linarith only [hlam, htr239b, htr2910a, htr3910a])
            obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
            rcases m.htr 2 3 10 (by decide) (by decide) with
              ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
            ·
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, hc037zy, htr0710a, htr2310a, htr237a, htr3710c])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                linarith only [hlam, hc346yz, htr2310a, htr236a, htr3610c, htr4610a])
              obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
              have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                linarith only [hlam, hc347yz, htr2310a, htr237a, htr3710c, htr4710a])
              obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
              have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                linarith only [hlam, hc367yz, htr2310a, htr237a, htr3710c, htr6710a])
              obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc378yz, htr2310a, htr238a, htr3810c, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc379yz, htr2310a, htr239a, htr3910c, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hd36a, hd710b, htr0710a, htr078a, htr367a, htr678a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hd57a, hd810b, htr078a, htr079a, htr579a, htr7810a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hd34a, hd810b, htr346a, htr467a, htr678a, htr7810a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                  linarith only [hlam, hc034zy, htr046a, htr346b, htr367a, htr467a])
                obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
                have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                  linarith only [hlam, hd34a, hd610b, htr046a, htr047a, htr347a, htr4610a])
                obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
                rcases m.htr 4 7 9 (by decide) (by decide) with
                  ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
                ·
                  linarith only [hlam, hc014yx, hc5910yz, htr012a, htr047a, htr125a, htr2510a, htr479a, htr7910a]
                ·
                  linarith only [hlam, hc017yx, hc5710yz, htr012a, htr079a, htr125a, htr2510a, htr4710a, htr479a]
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hc017yx, hc5710yz, htr012a, htr078a, htr125a, htr2510a, htr6710a, htr678a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hd57a, hd910b, htr078a, htr079a, htr578a, htr7910a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                  linarith only [hlam, hc014yx, hc5710yz, htr012a, htr046a, htr125a, htr2510a, htr467a, htr6710a])
                obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
                have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                  linarith only [hlam, hd34a, hd710b, htr046a, htr047a, htr346a, htr4710a])
                obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
                rcases m.htr 4 7 9 (by decide) (by decide) with
                  ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
                ·
                  linarith only [hlam, hd34a, hd710b, htr0710a, htr079a, htr347a, htr479a]
                ·
                  linarith only [hlam, hd45b, hd57a, htr045a, htr047a, htr479a, htr579a]
            ·
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                    linarith only [hlam, hd34a, hd89b, htr346a, htr467a, htr678a, htr789a])
                  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                    linarith only [hlam, hc034zy, htr046a, htr346b, htr367a, htr467a])
                  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
                  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                    linarith only [hlam, hc346yz, htr046a, htr047a, htr367a, htr467b])
                  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
                  rcases m.htr 4 7 8 (by decide) (by decide) with
                    ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                  ·
                    linarith only [hlam, hc014yx, hc589yz, htr012a, htr047a, htr125a, htr259a, htr478a, htr789a]
                  ·
                    linarith only [hlam, hc346yz, htr367a, htr467c, htr478a, htr678a]
                ·
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc457zy, htr478a, htr578b, htr589a, htr789a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc578yz, htr478a, htr479a, htr589a, htr789b])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc578yz, htr589a, htr678a, htr679a, htr789b])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a])
                  obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc578yz, htr479c, htr4910a, htr589a, htr789c, htr8910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                    linarith only [hlam, hc014yx, hc5910yz, htr012a, htr047a, htr125a, htr2510a, htr479a, htr7910a])
                  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
                  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
                    linarith only [hlam, hd34a, hd910b, htr047a, htr049a, htr347a, htr4910a])
                  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
                  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                    linarith only [hlam, hd34a, hd910b, htr346a, htr467a, htr679a, htr7910a])
                  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                  rcases m.htr 0 4 6 (by decide) (by decide) with
                    ⟨htr046a, htr046b, htr046c, _, _⟩ | ⟨htr046a, htr046b, htr046c, _, _⟩
                  ·
                    linarith only [hlam, hc346yz, htr046a, htr049a, htr367a, htr467b, htr479b]
                  ·
                    linarith only [hlam, hc034zy, htr046a, htr346b, htr367a, htr467a]
              ·
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, hc056zy, htr067a, htr567b, htr578a, htr678a])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc567yz, htr067a, htr068a, htr578a, htr678b])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc567yz, htr467a, htr468a, htr578a, htr678b])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, hc567yz, htr068c, htr089a, htr578a, htr678c, htr789a])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, htr068b, htr069c, htr089b])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr046a, htr046b, htr046c, _, _⟩
                  linarith only [hlam, hc014yx, hc589yz, htr012a, htr046a, htr125a, htr259a, htr468a, htr689a])
                obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
                have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  linarith only [hlam, hc016yx, hc5910yz, htr012a, htr068a, htr125a, htr2510a, htr689a, htr8910a])
                obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hc016yx, hc589yz, htr012a, htr069a, htr125a, htr259a, htr6910a, htr8910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 6 7 9 (by decide) (by decide) with
                  ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                ·
                  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                    linarith only [hlam, hd34a, hd79b, htr046a, htr047a, htr346a, htr467c, htr679a])
                  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
                  rcases m.htr 4 7 8 (by decide) (by decide) with
                    ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                  ·
                    linarith only [hlam, hd34a, hd79b, htr347a, htr478a, htr678a, htr679a]
                  ·
                    linarith only [hlam, hd45b, hd57a, htr045a, htr047a, htr478a, htr578a]
                ·
                  rcases m.htr 7 9 10 (by decide) (by decide) with
                    ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  ·
                    linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
                  ·
                    linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a]

theorem shard_621 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr247b : m.d 2 4 < m.d 2 7)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr349c : m.d 3 9 < m.d 4 9)
    : False :=
  proof_shard_621 m htr012a htr013a htr013b htr016a htr017a htr018a htr034c htr123a htr123b htr125a htr126a htr127a htr128a htr129a htr234a htr234b htr235a htr235b htr247b htr345c htr346a htr346b htr347a htr349c

#print axioms shard_621
end Jsp404.NoSatElevenDBMTerminal
