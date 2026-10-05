import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_311 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd48a := (m.hrange 4 8 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
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
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
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
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd12b, hd45a, htr012a, htr013a, htr123b, htr234a, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr012a, htr014a, htr145a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hd12b, hd46a, htr012a, htr013a, htr123b, htr234a, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr012a, htr014a, htr146a, htr346a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hd12b, hd48a, htr012a, htr013a, htr123b, htr234a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, hd12b, hd34a, htr012a, htr014a, htr148a, htr348a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  rcases m.htr 2 3 5 (by decide) (by decide) with
    ⟨htr235a, htr235b, htr235c, _, _⟩ | ⟨htr235a, htr235b, htr235c, _, _⟩
  ·
    have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr035a, htr035b, htr035c, _, _⟩
      linarith only [hlam, hd12b, hd34a, htr012a, htr013c, htr035a, htr234a, htr235a])
    obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
    rcases m.htr 2 3 6 (by decide) (by decide) with
      ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
    ·
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hc345xy, htr035a, htr036a, htr234a, htr236a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
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
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc346xy, htr126b, htr167a, htr234a, htr236b, htr367a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd34a, hd68b, htr234a, htr235a, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr368a, htr568a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc346xy, htr126b, htr168a, htr234a, htr236b, htr368a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr167a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc347xy, htr127b, htr178a, htr234a, htr237b, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd12b, hd89a, htr012a, htr016a, htr168a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hd12b, hd68a, htr012a, htr018a, htr189a, htr689a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc348xy, htr128b, htr189a, htr234a, htr238b, htr389a])
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
                  linarith only [hlam, hd12b, hd67a, htr012a, htr015a, htr125b, htr256a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hd12b, hd56a, htr012a, htr016a, htr167a, htr567a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc346xy, htr126b, htr167a, htr234a, htr236b, htr367a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd12b, hd68a, htr012a, htr015a, htr125b, htr256a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hd12b, hd56a, htr012a, htr016a, htr168a, htr568a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc346xy, htr126b, htr168a, htr234a, htr236b, htr368a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd34a, hd78b, htr234a, htr236a, htr367a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr378a, htr678a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc347xy, htr127b, htr178a, htr234a, htr237b, htr378a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd34a, hd89b, htr234a, htr236a, htr368a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hd34a, hd68b, htr234a, htr238a, htr389a, htr689a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc348xy, htr128b, htr189a, htr234a, htr238b, htr389a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd12b, hd78a, htr012a, htr018a, htr189a, htr789a]
                ·
                  linarith only [hlam, hd12b, hd89a, htr012a, htr017a, htr178a, htr789a]
            ·
              have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
                linarith only [hlam, htr023b, htr0310a, htr2310a])
              obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
              have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                linarith only [hlam, htr0310c, htr035b, htr0510b])
              obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                linarith only [hlam, htr0310c, htr036b, htr0610b])
              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
              have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                linarith only [hlam, hc126yx, htr012a, htr016c, htr0610a, htr1610a])
              obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
              have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                linarith only [hlam, htr035c, htr0510a, htr3510a])
              obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
              have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr356a, htr356b, htr356c, _, _⟩
                linarith only [hlam, hc5610yx, htr023b, htr035a, htr2310a, htr3510b, htr356a])
              obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hc345xy, htr125b, htr156a, htr234a, htr235b, htr356a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                linarith only [hlam, hd12b, hd56a, htr012a, htr016a, htr1610a, htr5610a]
              ·
                linarith only [hlam, hd12b, hd610a, htr012a, htr015a, htr156a, htr5610a]
          ·
            have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr039a, htr039b, htr039c, _, _⟩
              linarith only [hlam, htr023b, htr039a, htr239a])
            obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
            have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr059a, htr059b, htr059c, _, _⟩
              linarith only [hlam, htr035b, htr039c, htr059b])
            obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr036b, htr039c, htr069b])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr169a, htr169b, htr169c, _, _⟩
              linarith only [hlam, hc126yx, htr012a, htr016c, htr069a, htr169a])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr359a, htr359b, htr359c, _, _⟩
              linarith only [hlam, htr035c, htr059a, htr359a])
            obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc569yx, htr023b, htr035a, htr239a, htr356a, htr359b])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc345xy, htr125b, htr156a, htr234a, htr235b, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            rcases m.htr 5 6 9 (by decide) (by decide) with
              ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
            ·
              linarith only [hlam, hd12b, hd56a, htr012a, htr016a, htr169a, htr569a]
            ·
              linarith only [hlam, hd12b, hd69a, htr012a, htr015a, htr156a, htr569a]
        ·
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr023b, htr038a, htr238a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, htr035b, htr038c, htr058b])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr036b, htr038c, htr068b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc126yx, htr012a, htr016c, htr068a, htr168a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, htr035c, htr058a, htr358a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc568yx, htr023b, htr035a, htr238a, htr356a, htr358b])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc345xy, htr125b, htr156a, htr234a, htr235b, htr356a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          rcases m.htr 5 6 8 (by decide) (by decide) with
            ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
          ·
            linarith only [hlam, hd12b, hd56a, htr012a, htr016a, htr168a, htr568a]
          ·
            linarith only [hlam, hd12b, hd68a, htr012a, htr015a, htr156a, htr568a]
      ·
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr023b, htr037a, htr237a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, htr035b, htr037c, htr057b])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr036b, htr037c, htr067b])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc126yx, htr012a, htr016c, htr067a, htr167a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr357a, htr357b, htr357c, _, _⟩
          linarith only [hlam, htr035c, htr057a, htr357a])
        obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc567yx, htr023b, htr035a, htr237a, htr356a, htr357b])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc345xy, htr125b, htr156a, htr234a, htr235b, htr356a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          linarith only [hlam, hd12b, hd56a, htr012a, htr016a, htr167a, htr567a]
        ·
          linarith only [hlam, hd12b, hd67a, htr012a, htr015a, htr156a, htr567a]
    ·
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, htr023b, htr036a, htr236a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, htr035b, htr036c, htr056b])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, htr035c, htr056a, htr356a])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc567xy, htr023b, htr035a, htr236a, htr356b, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc345xy, htr125b, htr157a, htr234a, htr235b, htr357a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hc568xy, htr023b, htr035a, htr236a, htr356b, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc345xy, htr125b, htr158a, htr234a, htr235b, htr358a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr359a, htr359b, htr359c, _, _⟩
        linarith only [hlam, hc569xy, htr023b, htr035a, htr236a, htr356b, htr359a])
      obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
      have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr159a, htr159b, htr159c, _, _⟩
        linarith only [hlam, hc345xy, htr125b, htr159a, htr234a, htr235b, htr359a])
      obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr012a, htr013a, htr123b, htr236a, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc356yx, htr035a, htr036c, htr067a, htr367a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr012a, htr013a, htr123b, htr236a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc356yx, htr035a, htr036c, htr068a, htr368a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
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
        linarith only [hlam, hd12b, hd78a, htr012a, htr015a, htr157a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hd12b, hd57a, htr012a, htr017a, htr178a, htr578a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd12b, hd89a, htr012a, htr015a, htr158a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc124yx, hc578yz, htr012a, htr015a, htr146a, htr158a, htr467a, htr678a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc126yx, hc568yz, htr012a, htr015a, htr016b, htr067a, htr158a, htr467a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc126yx, hc589yz, htr012a, htr015a, htr016b, htr067a, htr159a, htr678a, htr789a]
        ·
          linarith only [hlam, hc126yx, hc578yz, htr012a, htr015a, htr016b, htr068a, htr158a, htr689a, htr789a]
      ·
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc126yx, hc567yz, htr012a, htr015a, htr016b, htr068a, htr157a, htr467a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc124yx, hc589yz, htr012a, htr015a, htr146a, htr159a, htr468a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc127yx, hc568yz, htr012a, htr015a, htr158a, htr178a, htr689a, htr789a]
        ·
          linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd12b, hd56a, htr012a, htr013a, htr123b, htr235a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hd12b, hd35a, htr012a, htr015a, htr156a, htr356a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd12b, hd57a, htr012a, htr013a, htr123b, htr235a, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hd12b, hd35a, htr012a, htr015a, htr157a, htr357a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hd12b, hd58a, htr012a, htr013a, htr123b, htr235a, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr158a, htr158b, htr158c, _, _⟩
      linarith only [hlam, hd12b, hd35a, htr012a, htr015a, htr158a, htr358a])
    obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
    rcases m.htr 2 3 6 (by decide) (by decide) with
      ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
    ·
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd12b, hd34a, htr012a, htr013c, htr036a, htr234a, htr236a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc345yz, htr235a, htr236a, htr356c, htr456a])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      rcases m.htr 2 3 7 (by decide) (by decide) with
        ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
      ·
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc346xy, htr036a, htr037a, htr234a, htr237a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr457a, htr457b, htr457c, _, _⟩
          linarith only [hlam, hc345yz, htr235a, htr237a, htr357c, htr457a])
        obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
        rcases m.htr 2 3 8 (by decide) (by decide) with
          ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
        ·
          rcases m.htr 2 3 9 (by decide) (by decide) with
            ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
          ·
            rcases m.htr 2 3 10 (by decide) (by decide) with
              ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
            ·
              rcases m.htr 2 6 7 (by decide) (by decide) with
                ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
              ·
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc346xy, htr234a, htr236b, htr267a, htr367a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr367a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc124yx, hc678yx, htr012a, htr016a, htr145a, htr168a, htr456a, htr567a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc346xy, htr126b, htr168a, htr234a, htr236b, htr368a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd34a, hd67b, htr234a, htr236a, htr368a, htr567a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc124yx, hc678zy, htr012a, htr017a, htr145a, htr178a, htr456a, htr568a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc347xy, htr127b, htr178a, htr234a, htr237b, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd34a, hd78b, htr234a, htr236a, htr367a, htr678a]
                ·
                  linarith only [hlam, hd34a, hd67b, htr234a, htr237a, htr378a, htr678a]
              ·
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc124yx, hc678xy, htr012a, htr016a, htr126b, htr145a, htr267a, htr456a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr234a, htr236a, htr368a, htr568a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc346xy, htr126b, htr168a, htr234a, htr236b, htr368a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc124yx, hc678yz, htr012a, htr016a, htr145a, htr168a, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd34a, hd57b, htr234a, htr237a, htr378a, htr578a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc347xy, htr127b, htr178a, htr234a, htr237b, htr378a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a]
                ·
                  linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr126b, htr267a, htr678a]
            ·
              have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
                linarith only [hlam, htr023b, htr0310a, htr2310a])
              obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                linarith only [hlam, htr0310c, htr036b, htr0610b])
              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, htr0310c, htr037b, htr0710b])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hc127yx, htr012a, htr017c, htr0710a, htr1710a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
                linarith only [hlam, htr036c, htr0610a, htr3610a])
              obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc6710yx, htr023b, htr036a, htr2310a, htr3610b, htr367a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc346xy, htr126b, htr167a, htr234a, htr236b, htr367a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              rcases m.htr 6 7 10 (by decide) (by decide) with
                ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              ·
                linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr1710a, htr6710a]
              ·
                linarith only [hlam, hd12b, hd710a, htr012a, htr016a, htr167a, htr6710a]
          ·
            have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr039a, htr039b, htr039c, _, _⟩
              linarith only [hlam, htr023b, htr039a, htr239a])
            obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr036b, htr039c, htr069b])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, htr037b, htr039c, htr079b])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc127yx, htr012a, htr017c, htr079a, htr179a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr369a, htr369b, htr369c, _, _⟩
              linarith only [hlam, htr036c, htr069a, htr369a])
            obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc679yx, htr023b, htr036a, htr239a, htr367a, htr369b])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc346xy, htr126b, htr167a, htr234a, htr236b, htr367a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr179a, htr679a]
            ·
              linarith only [hlam, hd12b, hd79a, htr012a, htr016a, htr167a, htr679a]
        ·
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, htr023b, htr038a, htr238a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr036b, htr038c, htr068b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr037b, htr038c, htr078b])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc127yx, htr012a, htr017c, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, htr036c, htr068a, htr368a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc678yx, htr023b, htr036a, htr238a, htr367a, htr368b])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc346xy, htr126b, htr167a, htr234a, htr236b, htr367a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd12b, hd67a, htr012a, htr017a, htr178a, htr678a]
          ·
            linarith only [hlam, hd12b, hd78a, htr012a, htr016a, htr167a, htr678a]
      ·
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, htr023b, htr037a, htr237a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr036b, htr037c, htr067b])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, htr036c, htr067a, htr367a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc678xy, htr023b, htr036a, htr237a, htr367b, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc346xy, htr126b, htr168a, htr234a, htr236b, htr368a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc679xy, htr023b, htr036a, htr237a, htr367b, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
          linarith only [hlam, hc346xy, htr126b, htr169a, htr234a, htr236b, htr369a])
        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
        have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
          linarith only [hlam, hc6710xy, htr023b, htr036a, htr237a, htr3610a, htr367b])
        obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
        have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
          linarith only [hlam, hc346xy, htr126b, htr1610a, htr234a, htr236b, htr3610a])
        obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr012a, htr013a, htr123b, htr237a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc367yx, htr036a, htr037c, htr078a, htr378a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, htr367b, htr378a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12b, hd89a, htr012a, htr016a, htr168a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hd12b, hd68a, htr012a, htr018a, htr189a, htr689a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hd12b, hd810a, htr012a, htr016a, htr168a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hd12b, hd68a, htr012a, htr018a, htr1810a, htr6810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc127yx, hc468zy, htr012a, htr016a, htr017b, htr078a, htr168a, htr489a, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc128yx, hc689yz, htr012a, htr016a, htr169a, htr1810a, htr4810a, htr489a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc125yx, hc689yz, htr012a, htr016a, htr157a, htr169a, htr578a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr458a, htr458b, htr458c, _, _⟩
            linarith only [hlam, hc125yx, hc357yz, htr012a, htr013a, htr123b, htr158a, htr237a, htr457a, htr458a])
          obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
          rcases m.htr 5 8 10 (by decide) (by decide) with
            ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          ·
            linarith only [hlam, hc124yx, hc6810yz, htr012a, htr016a, htr145a, htr1610a, htr458a, htr5810a]
          ·
            linarith only [hlam, hc124yx, hc568zy, htr012a, htr016a, htr148a, htr168a, htr4810a, htr5810a]
        ·
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc124yx, hc678yz, htr012a, htr016a, htr148a, htr168a, htr489a, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc128yx, hc6810yz, htr012a, htr016a, htr1610a, htr189a, htr4810a, htr489a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hc124yx, hc678yz, htr012a, htr016a, htr145a, htr168a, htr457a, htr578a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr458a, htr458b, htr458c, _, _⟩
            linarith only [hlam, hc125yx, hc568zy, htr012a, htr016a, htr157a, htr168a, htr457a, htr458a])
          obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
          rcases m.htr 5 8 10 (by decide) (by decide) with
            ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          ·
            linarith only [hlam, hc125yx, hc468zy, htr012a, htr016a, htr158a, htr168a, htr4810a, htr5810a]
          ·
            linarith only [hlam, hd56b, hd68a, htr456a, htr458a, htr5810a, htr6810a]
    ·
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hd12b, hd67a, htr012a, htr013a, htr123b, htr236a, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd12b, hd68a, htr012a, htr013a, htr123b, htr236a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hd12b, hd36a, htr012a, htr016a, htr168a, htr368a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      rcases m.htr 4 5 6 (by decide) (by decide) with
        ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
      ·
        have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr457a, htr457b, htr457c, _, _⟩
          linarith only [hlam, hc125yx, hc356yz, htr012a, htr013a, htr123b, htr157a, htr236a, htr456a, htr457a])
        obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, hc125yx, hc356yz, htr012a, htr013a, htr123b, htr158a, htr236a, htr456a, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc124yx, hc367yz, htr012a, htr013a, htr137a, htr145a, htr456a, htr567a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc123yx, htr012a, htr013c, htr037a, htr137a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd34a, hd78b, htr345a, htr456a, htr567a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd34a, hd67b, htr123b, htr137a, htr234a, htr378a, htr678a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc347xy, htr123b, htr137b, htr178a, htr234a, htr378a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr568a, htr568b, htr568c, _, _⟩
            linarith only [hlam, hc124yx, hc678zy, htr012a, htr017a, htr145a, htr178a, htr456a, htr568a])
          obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc356yz, htr023b, htr038a, htr236a, htr368c, htr568a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc347xy, htr037a, htr038a, htr123b, htr138a, htr234a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc789xy, htr037a, htr038a, htr378b, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hc347xy, htr123b, htr137b, htr179a, htr234a, htr379a])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd12b, hd89a, htr012a, htr013a, htr138a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc124yx, hc789yz, htr012a, htr017a, htr145a, htr179a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 6 8 9 (by decide) (by decide) with
            ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
          ·
            linarith only [hlam, hc126yx, hc578zy, htr012a, htr017a, htr168a, htr178a, htr589a, htr689a]
          ·
            linarith only [hlam, hc356yz, htr368b, htr389a, htr568a, htr689a]
        ·
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc356yz, htr123b, htr137a, htr236a, htr367c, htr567a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr012a, htr013a, htr137a, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd12b, hd79a, htr012a, htr013a, htr137a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc124yx, hc378yz, htr012a, htr013a, htr138a, htr145a, htr457a, htr578a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc356yz, htr367b, htr379a, htr567a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc356yz, htr367a, htr567c, htr579a, htr679a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc124yx, hc789zy, htr012a, htr018a, htr145a, htr189a, htr457a, htr579a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc348xy, htr123b, htr138b, htr189a, htr234a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd34a, hd89b, htr345a, htr457a, htr578a, htr789a]
          ·
            linarith only [hlam, hd34a, hd78b, htr123b, htr138a, htr234a, htr389a, htr789a]
      ·
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc345yz, htr356b, htr368a, htr456a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        rcases m.htr 4 5 7 (by decide) (by decide) with
          ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
        ·
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc125yx, hc357yz, htr012a, htr013a, htr137a, htr156a, htr456a, htr457a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr037a, htr037b, htr037c, _, _⟩
            linarith only [hlam, hc123yx, htr012a, htr013c, htr037a, htr137a])
          obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd35a, hd78b, htr356a, htr456a, htr457a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd34a, hd57b, htr123b, htr137a, htr234a, htr378a, htr578a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc347xy, htr123b, htr137b, htr178a, htr234a, htr378a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr458a, htr458b, htr458c, _, _⟩
            linarith only [hlam, hc125yx, hc578zy, htr012a, htr017a, htr156a, htr178a, htr456a, htr458a])
          obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
          have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr038a, htr038b, htr038c, _, _⟩
            linarith only [hlam, hc345yz, htr023b, htr038a, htr235a, htr358c, htr458a])
          obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc347xy, htr037a, htr038a, htr123b, htr138a, htr234a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hc789xy, htr037a, htr038a, htr378b, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hc347xy, htr123b, htr137b, htr179a, htr234a, htr379a])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd12b, hd89a, htr012a, htr013a, htr138a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc345yz, htr358b, htr389a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 6 8 9 (by decide) (by decide) with
            ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
          ·
            linarith only [hlam, hc125yx, hc789yz, htr012a, htr017a, htr156a, htr179a, htr568a, htr689a]
          ·
            linarith only [hlam, hc125yx, hc678zy, htr012a, htr017a, htr158a, htr178a, htr589a, htr689a]
        ·
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hc345yz, htr123b, htr137a, htr235a, htr357c, htr457a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr012a, htr013a, htr137a, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd12b, hd79a, htr012a, htr013a, htr137a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc345yz, htr357b, htr378a, htr457a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc345yz, htr357b, htr379a, htr457a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hc125yx, hc367yz, htr012a, htr013a, htr137a, htr157a, htr578a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hc125yx, hc378yz, htr012a, htr013a, htr138a, htr156a, htr567a, htr678a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr458a, htr458b, htr458c, _, _⟩
            linarith only [hlam, hc345yz, htr123b, htr138a, htr235a, htr358c, htr458a])
          obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd35a, hd89b, htr356a, htr456a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd34a, hd58b, htr123b, htr138a, htr234a, htr389a, htr589a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc348xy, htr123b, htr138b, htr189a, htr234a, htr389a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hc125yx, hc789zy, htr012a, htr018a, htr156a, htr189a, htr567a, htr679a]
          ·
            linarith only [hlam, hc125yx, hc367yz, htr012a, htr013a, htr137a, htr157a, htr579a, htr679a]

theorem shard_311 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128b : m.d 2 8 < m.d 1 8)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_311 m htr012a htr013a htr013c htr014a htr015a htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr023b htr123b htr125b htr126b htr127b htr128b htr234a

#print axioms shard_311
end Jsp404.NoSatElevenDBMTerminal
