import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_153 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr348b : m.d 4 8 < m.d 3 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
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
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
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
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, htr023b, htr036a, htr236a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, htr123b, htr136a, htr236a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc345yx, htr013c, htr037a, htr134a, htr235a, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr035c, htr037b, htr057c])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr036c, htr037b, htr067c])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr025b, htr057a, htr235b, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc567xy, htr023b, htr037a, htr235a, htr356a, htr357c])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc345yx, htr134a, htr135c, htr156a, htr356a])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr026b, htr067a, htr236b, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc678yx, htr023b, htr037a, htr236a, htr367c, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hc346yx, htr134a, htr136c, htr168a, htr368a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hc356yz, htr236a, htr237a, htr367c, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr567a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hc012xy, hc678zy, htr015a, htr024a, htr156a, htr247a, htr478a, htr568a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hc012xy, hc467yz, htr015a, htr027a, htr156a, htr278a, htr478a, htr567a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hc357xy, htr235a, htr237b, htr278a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a]
    ·
      linarith only [hlam, hd35a, hd67b, htr235a, htr237a, htr378a, htr678a]
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr023b, htr037a, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr123b, htr137a, htr237a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    rcases m.htr 2 3 8 (by decide) (by decide) with
      ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, hc345yx, htr013c, htr038a, htr134a, htr235a, htr238a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr035c, htr038b, htr058c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr036c, htr038b, htr068c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr037c, htr038b, htr078c])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, htr025b, htr058a, htr235b, htr358a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hc568xy, htr023b, htr038a, htr235a, htr356a, htr358c])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hc345yx, htr134a, htr135c, htr156a, htr356a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr026b, htr068a, htr236b, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc678xy, htr023b, htr038a, htr236a, htr367a, htr368c])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc346yx, htr134a, htr136c, htr167a, htr367a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr027b, htr078a, htr237b, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc356yz, htr236a, htr238a, htr368c, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hd01a, hd68b, htr016a, htr167a, htr567a, htr568a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a]
      ·
        linarith only [hlam, hc367yz, htr237a, htr238a, htr378c, htr678a]
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr023b, htr038a, htr238a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr123b, htr138a, htr238a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      rcases m.htr 2 3 9 (by decide) (by decide) with
        ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
      ·
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, hc345yx, htr013c, htr039a, htr134a, htr235a, htr239a])
        obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, htr035c, htr039b, htr059c])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, htr036c, htr039b, htr069c])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr037c, htr039b, htr079c])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, htr025b, htr059a, htr235b, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc569xy, htr023b, htr039a, htr235a, htr356a, htr359c])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hc345yx, htr134a, htr135c, htr156a, htr356a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, htr026b, htr069a, htr236b, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc679xy, htr023b, htr039a, htr236a, htr367a, htr369c])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc346yx, htr134a, htr136c, htr167a, htr367a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, htr027b, htr079a, htr237b, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc356yz, htr236a, htr239a, htr369c, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd01a, hd69b, htr016a, htr167a, htr567a, htr569a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hd01a, hd79b, htr015a, htr156a, htr567a, htr679a]
        ·
          linarith only [hlam, hc367yz, htr237a, htr239a, htr379c, htr679a]
      ·
        rcases m.htr 2 3 10 (by decide) (by decide) with
          ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
        ·
          have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
            linarith only [hlam, hc345yx, htr013c, htr0310a, htr134a, htr2310a, htr235a])
          obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
            linarith only [hlam, htr0310b, htr035c, htr0510c])
          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
            linarith only [hlam, htr0310b, htr036c, htr0610c])
          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0310b, htr037c, htr0710c])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
            linarith only [hlam, htr025b, htr0510a, htr235b, htr3510a])
          obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc5610xy, htr023b, htr0310a, htr235a, htr3510c, htr356a])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hc345yx, htr134a, htr135c, htr156a, htr356a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
            linarith only [hlam, htr026b, htr0610a, htr236b, htr3610a])
          obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc6710xy, htr023b, htr0310a, htr236a, htr3610c, htr367a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc346yx, htr134a, htr136c, htr167a, htr367a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, htr027b, htr0710a, htr237b, htr3710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, hc356yz, htr2310a, htr236a, htr3610c, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hd01a, hd610b, htr016a, htr167a, htr5610a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          rcases m.htr 6 7 10 (by decide) (by decide) with
            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          ·
            linarith only [hlam, hd01a, hd710b, htr015a, htr156a, htr567a, htr6710a]
          ·
            linarith only [hlam, hc367yz, htr2310a, htr237a, htr3710c, htr6710a]
        ·
          rcases m.htr 4 5 6 (by decide) (by decide) with
            ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
          ·
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hd34b, hd45a, htr134a, htr135a, htr356a, htr456a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc345yx, htr015c, htr056a, htr134a, htr135c, htr356a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hc345yx, htr134a, htr135c, htr156a, htr356a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            rcases m.htr 1 5 7 (by decide) (by decide) with
              ⟨htr157a, htr157b, htr157c, _, _⟩ | ⟨htr157a, htr157b, htr157c, _, _⟩
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, htr015c, htr057a, htr157a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              rcases m.htr 1 5 8 (by decide) (by decide) with
                ⟨htr158a, htr158b, htr158c, _, _⟩ | ⟨htr158a, htr158b, htr158c, _, _⟩
              ·
                rcases m.htr 1 5 9 (by decide) (by decide) with
                  ⟨htr159a, htr159b, htr159c, _, _⟩ | ⟨htr159a, htr159b, htr159c, _, _⟩
                ·
                  rcases m.htr 1 5 10 (by decide) (by decide) with
                    ⟨htr1510a, htr1510b, htr1510c, _, _⟩ | ⟨htr1510a, htr1510b, htr1510c, _, _⟩
                  ·
                    rcases m.htr 5 6 7 (by decide) (by decide) with
                      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                    ·
                      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                        linarith only [hlam, hc012xy, hc678yx, htr015a, htr023a, htr156a, htr236a, htr368a, htr567a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                        linarith only [hlam, hc346yx, htr134a, htr136c, htr168a, htr368a])
                      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                        linarith only [hlam, hc012xy, hc679yx, htr015a, htr023a, htr156a, htr236a, htr369a, htr567a])
                      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                        linarith only [hlam, hc346yx, htr134a, htr136c, htr169a, htr369a])
                      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                        linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr567a, htr568a])
                      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc012xy, hc678zy, htr015a, htr023a, htr156a, htr237a, htr378a, htr568a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                        linarith only [hlam, hc347yx, htr134a, htr137c, htr178a, htr378a])
                      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, hd01a, hd67b, htr016a, htr169a, htr567a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc012xy, hc689zy, htr015a, htr023a, htr156a, htr238a, htr389a, htr569a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd01a, hd89b, htr015a, htr156a, htr568a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd01a, hd68b, htr017a, htr178a, htr689a, htr789a]
                      ·
                        linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a]
                    ·
                      rcases m.htr 4 6 7 (by decide) (by decide) with
                        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                      ·
                        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                          linarith only [hlam, hd12b, hd46a, htr123a, htr236a, htr367a, htr467a])
                        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                          linarith only [hlam, hc346yx, htr013c, htr036c, htr067a, htr134a, htr367a])
                        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                          linarith only [hlam, hc346yx, htr134a, htr136c, htr167a, htr367a])
                        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                          linarith only [hlam, hd01a, hd68b, htr016a, htr167a, htr567a, htr568a])
                        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                        rcases m.htr 4 6 8 (by decide) (by decide) with
                          ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                        ·
                          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                            linarith only [hlam, hc456yz, htr067a, htr068a, htr468a, htr567a])
                          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                            linarith only [hlam, hc456yz, htr167a, htr168a, htr468a, htr567a])
                          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                          rcases m.htr 4 6 9 (by decide) (by decide) with
                            ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                          ·
                            rcases m.htr 4 6 10 (by decide) (by decide) with
                              ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                            ·
                              rcases m.htr 6 7 8 (by decide) (by decide) with
                                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                              ·
                                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                                  linarith only [hlam, hc012xy, hc789yx, htr016a, htr023a, htr167a, htr237a, htr379a, htr678a])
                                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                                  linarith only [hlam, hc347yx, htr134a, htr137c, htr179a, htr379a])
                                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                                  linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
                                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                                  linarith only [hlam, hd01a, hd78b, htr017a, htr179a, htr578a, htr579a])
                                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                                  linarith only [hlam, hc012xy, hc789zy, htr015a, htr023a, htr157a, htr238a, htr389a, htr579a])
                                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                                  linarith only [hlam, hc456yz, htr348b, htr389a, htr468b, htr568a, htr689a])
                                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                                rcases m.htr 7 8 9 (by decide) (by decide) with
                                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                                ·
                                  linarith only [hlam, hd01a, hd89b, htr016a, htr167a, htr678a, htr789a]
                                ·
                                  linarith only [hlam, hd01a, hd78b, htr016a, htr168a, htr689a, htr789a]
                              ·
                                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                                  linarith only [hlam, hc456yz, htr347b, htr378a, htr467b, htr567a, htr678a])
                                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                                  linarith only [hlam, hc012xy, hc789xy, htr016a, htr023a, htr167a, htr237a, htr378a, htr679a])
                                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                                  linarith only [hlam, hc456yz, htr347b, htr379a, htr467b, htr567a, htr679a])
                                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                                  linarith only [hlam, hc012xy, hc789yz, htr015a, htr023a, htr158a, htr237a, htr379a, htr589a])
                                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                                  linarith only [hlam, hc012xy, hc578zy, htr018a, htr023a, htr189a, htr237a, htr378a, htr589a])
                                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                                  linarith only [hlam, hc348yx, htr134a, htr138c, htr189a, htr389a])
                                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                                rcases m.htr 7 8 9 (by decide) (by decide) with
                                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                                ·
                                  linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr389a, htr789a]
                                ·
                                  linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]
                            ·
                              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                                linarith only [hlam, htr046b, htr0610a, htr4610a])
                              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                                linarith only [hlam, htr0610c, htr067b, htr0710b])
                              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                              have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                                linarith only [hlam, htr0610c, htr068b, htr0810b])
                              obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                              have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                                linarith only [hlam, hc347yx, htr013c, htr037c, htr0710a, htr134a, htr3710a])
                              obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                              have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                                linarith only [hlam, hc348yx, htr013c, htr038c, htr0810a, htr134a, htr3810a])
                              obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                                linarith only [hlam, hc012xy, hc7810yx, htr016a, htr023a, htr167a, htr237a, htr3710a, htr678a])
                              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                                linarith only [hlam, hc456yz, htr347b, htr378a, htr467b, htr567a, htr678a])
                              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                              rcases m.htr 7 8 10 (by decide) (by decide) with
                                ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                              ·
                                linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr3810a, htr7810a]
                              ·
                                linarith only [hlam, hd12b, hd810a, htr123a, htr237a, htr378a, htr7810a]
                          ·
                            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                              linarith only [hlam, htr046b, htr069a, htr469a])
                            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                              linarith only [hlam, htr067b, htr069c, htr079b])
                            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                              linarith only [hlam, htr068b, htr069c, htr089b])
                            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                              linarith only [hlam, hc347yx, htr013c, htr037c, htr079a, htr134a, htr379a])
                            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                              linarith only [hlam, hc348yx, htr013c, htr038c, htr089a, htr134a, htr389a])
                            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                              linarith only [hlam, hc012xy, hc789yx, htr016a, htr023a, htr167a, htr237a, htr379a, htr678a])
                            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                              linarith only [hlam, hc456yz, htr347b, htr378a, htr467b, htr567a, htr678a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            rcases m.htr 7 8 9 (by decide) (by decide) with
                              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                            ·
                              linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr389a, htr789a]
                            ·
                              linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]
                        ·
                          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                            linarith only [hlam, htr046b, htr068a, htr468a])
                          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                            linarith only [hlam, htr067b, htr068c, htr078b])
                          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                            linarith only [hlam, htr146b, htr168a, htr468a])
                          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                            linarith only [hlam, hc347yx, htr013c, htr037c, htr078a, htr134a, htr378a])
                          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hc012xy, hc789xy, htr016a, htr023a, htr167a, htr237a, htr378a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                            linarith only [hlam, hc456yz, htr347b, htr379a, htr467b, htr567a, htr679a])
                          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc012xy, hc789yz, htr015a, htr023a, htr158a, htr237a, htr379a, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                            linarith only [hlam, hc012xy, hc568zy, htr018a, htr024a, htr189a, htr246a, htr468a, htr589a])
                          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd56b, hd78a, htr167a, htr168c, htr189a, htr567a, htr789a]
                          ·
                            linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]
                      ·
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hd12b, hd78a, htr124a, htr246a, htr467a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                          linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a])
                        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                          linarith only [hlam, hc347yx, htr134a, htr137c, htr178a, htr378a])
                        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc012xy, hc567zy, htr017a, htr024a, htr178a, htr246a, htr467a, htr578a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                          linarith only [hlam, hc012xy, hc678yz, htr015a, htr023a, htr157a, htr236a, htr368a, htr578a])
                        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc012xy, hc789yx, htr015a, htr023a, htr157a, htr237a, htr379a, htr578a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc347yx, htr134a, htr137c, htr179a, htr379a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hc012xy, hc567zy, htr017a, htr024a, htr179a, htr246a, htr467a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                          linarith only [hlam, hc012xy, hc789zy, htr015a, htr023a, htr157a, htr238a, htr389a, htr579a])
                        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc678xy, htr346b, htr368b, htr389a, htr467a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd01a, hd89b, htr015a, htr157a, htr578a, htr789a]
                        ·
                          linarith only [hlam, hd67a, hd78b, htr346b, htr368a, htr467a, htr689a, htr789a]
                  ·
                    have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                      linarith only [hlam, hc345yx, htr025b, htr0510a, htr134a, htr135c, htr1510a, htr235b])
                    obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                    have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                      linarith only [hlam, htr0510c, htr056b, htr0610b])
                    obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                    have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                      linarith only [hlam, htr0510c, htr057b, htr0710b])
                    obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                    have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                      linarith only [hlam, hc345yx, htr134a, htr135c, htr1510a, htr3510a])
                    obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
                    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
                      linarith only [hlam, hc346yx, htr013c, htr036c, htr0610a, htr134a, htr3610a])
                    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
                    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                      linarith only [hlam, hc347yx, htr013c, htr037c, htr0710a, htr134a, htr3710a])
                    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hc012xy, hc6710yx, htr015a, htr023a, htr156a, htr236a, htr3610a, htr567a])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                      linarith only [hlam, hc5610yx, htr3510a, htr356b, htr367a, htr567a])
                    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                    rcases m.htr 6 7 10 (by decide) (by decide) with
                      ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    ·
                      linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr3710a, htr6710a]
                    ·
                      linarith only [hlam, hd12b, hd710a, htr123a, htr236a, htr367a, htr6710a]
                ·
                  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                    linarith only [hlam, hc345yx, htr025b, htr059a, htr134a, htr135c, htr159a, htr235b])
                  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                    linarith only [hlam, htr056b, htr059c, htr069b])
                  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, htr057b, htr059c, htr079b])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
                    linarith only [hlam, hc345yx, htr134a, htr135c, htr159a, htr359a])
                  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
                  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                    linarith only [hlam, hc346yx, htr013c, htr036c, htr069a, htr134a, htr369a])
                  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                    linarith only [hlam, hc347yx, htr013c, htr037c, htr079a, htr134a, htr379a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, hc012xy, hc679yx, htr015a, htr023a, htr156a, htr236a, htr369a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                    linarith only [hlam, hc569yx, htr356b, htr359a, htr367a, htr567a])
                  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                  rcases m.htr 6 7 9 (by decide) (by decide) with
                    ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                  ·
                    linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr379a, htr679a]
                  ·
                    linarith only [hlam, hd12b, hd79a, htr123a, htr236a, htr367a, htr679a]
              ·
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc345yx, htr025b, htr058a, htr134a, htr135c, htr158a, htr235b])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, htr056b, htr058c, htr068b])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr057b, htr058c, htr078b])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                  linarith only [hlam, hc345yx, htr134a, htr135c, htr158a, htr358a])
                obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hc346yx, htr013c, htr036c, htr068a, htr134a, htr368a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc347yx, htr013c, htr037c, htr078a, htr134a, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hc012xy, hc678yx, htr015a, htr023a, htr156a, htr236a, htr368a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                  linarith only [hlam, hc568yx, htr356b, htr358a, htr367a, htr567a])
                obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd12b, hd67a, htr123a, htr237a, htr378a, htr678a]
                ·
                  linarith only [hlam, hd12b, hd78a, htr123a, htr236a, htr367a, htr678a]
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hc345yx, htr025b, htr057a, htr134a, htr135c, htr157a, htr235b])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, htr056b, htr057c, htr067b])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                linarith only [hlam, hc345yx, htr134a, htr135c, htr157a, htr357a])
              obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc346yx, htr013c, htr036c, htr067a, htr134a, htr367a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc012xy, hc678xy, htr015a, htr023a, htr156a, htr236a, htr367a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc567yx, htr356b, htr357a, htr368a, htr568a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                linarith only [hlam, hc012xy, hc679xy, htr015a, htr023a, htr156a, htr236a, htr367a, htr569a])
              obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
              have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                linarith only [hlam, hc567yx, htr356b, htr357a, htr369a, htr569a])
              obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd34b, hd78a, htr134a, htr135a, htr357a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc567yx, htr156a, htr157c, htr178a, htr578a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd12b, hd89a, htr123a, htr236a, htr368a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hd12b, hd68a, htr123a, htr238a, htr389a, htr689a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc348yx, htr134a, htr138c, htr189a, htr389a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hc012xy, hc689yz, htr017a, htr023a, htr178a, htr236a, htr369a, htr789a]
              ·
                linarith only [hlam, hc012xy, hc678yz, htr018a, htr023a, htr189a, htr236a, htr368a, htr789a]
          ·
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd34b, hd67a, htr134a, htr135a, htr345b, htr456a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hd12b, hd56a, htr123a, htr236a, htr367a, htr567a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc346yx, htr134a, htr136c, htr167a, htr367a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd34b, hd68a, htr134a, htr135a, htr345b, htr456a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hd12b, hd56a, htr123a, htr236a, htr368a, htr568a])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
              linarith only [hlam, hc346yx, htr134a, htr136c, htr168a, htr368a])
            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
            rcases m.htr 4 5 7 (by decide) (by decide) with
              ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
            ·
              have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr015c, htr057a, htr134a, htr135c, htr456a, htr457a])
              obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr134a, htr135c, htr157a, htr456a, htr457a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              rcases m.htr 4 5 8 (by decide) (by decide) with
                ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
              ·
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, hc567xy, htr057a, htr058a, htr456a, htr458a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, hc567xy, htr157a, htr158a, htr456a, htr458a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                rcases m.htr 4 5 9 (by decide) (by decide) with
                  ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
                ·
                  rcases m.htr 4 5 10 (by decide) (by decide) with
                    ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                  ·
                    rcases m.htr 4 7 8 (by decide) (by decide) with
                      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                    ·
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc012xy, hc789yx, htr015a, htr023a, htr157a, htr237a, htr379a, htr578a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc567xy, htr347b, htr379a, htr456a, htr457b, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc012xy, hc789zy, htr015a, htr023a, htr157a, htr238a, htr389a, htr579a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc568xy, htr348b, htr389a, htr456a, htr458b, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd56a, hd89b, htr456a, htr457a, htr578a, htr789a]
                      ·
                        linarith only [hlam, hd56a, hd78b, htr456a, htr458a, htr589a, htr789a]
                    ·
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc012xy, hc789xy, htr015a, htr024a, htr157a, htr247a, htr478a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                        linarith only [hlam, hc567xy, htr347b, htr379a, htr456a, htr457b, htr579a])
                      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc012xy, hc789yz, htr015a, htr023a, htr158a, htr237a, htr379a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc568xy, htr348b, htr389a, htr456a, htr458b, htr589a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr389a, htr789a]
                      ·
                        linarith only [hlam, hd12b, hd89a, htr124a, htr247a, htr478a, htr789a]
                  ·
                    have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                      linarith only [hlam, htr045b, htr0510a, htr4510a])
                    obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                    have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                      linarith only [hlam, htr0510c, htr057b, htr0710b])
                    obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, htr0510c, htr058b, htr0810b])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                      linarith only [hlam, hc347yx, htr013c, htr037c, htr0710a, htr134a, htr3710a])
                    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                    have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                      linarith only [hlam, hc348yx, htr013c, htr038c, htr0810a, htr134a, htr3810a])
                    obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hc012xy, hc7810yx, htr015a, htr023a, htr157a, htr237a, htr3710a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc567xy, htr347b, htr378a, htr456a, htr457b, htr578a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    rcases m.htr 7 8 10 (by decide) (by decide) with
                      ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    ·
                      linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr3810a, htr7810a]
                    ·
                      linarith only [hlam, hd12b, hd810a, htr123a, htr237a, htr378a, htr7810a]
                ·
                  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                    linarith only [hlam, htr045b, htr059a, htr459a])
                  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, htr057b, htr059c, htr079b])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, htr058b, htr059c, htr089b])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                    linarith only [hlam, hc347yx, htr013c, htr037c, htr079a, htr134a, htr379a])
                  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                  have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                    linarith only [hlam, hc348yx, htr013c, htr038c, htr089a, htr134a, htr389a])
                  obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc012xy, hc789yx, htr015a, htr023a, htr157a, htr237a, htr379a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hc567xy, htr347b, htr378a, htr456a, htr457b, htr578a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd12b, hd78a, htr123a, htr238a, htr389a, htr789a]
                  ·
                    linarith only [hlam, hd12b, hd89a, htr123a, htr237a, htr378a, htr789a]
              ·
                have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                  linarith only [hlam, htr045b, htr058a, htr458a])
                obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr057b, htr058c, htr078b])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, htr145b, htr158a, htr458a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc347yx, htr013c, htr037c, htr078a, htr134a, htr378a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc012xy, hc789xy, htr015a, htr023a, htr157a, htr237a, htr378a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc567xy, htr347b, htr379a, htr456a, htr457b, htr579a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd34b, hd89a, htr134a, htr135a, htr345b, htr458a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc578yx, htr157a, htr158c, htr189a, htr589a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                rcases m.htr 6 8 9 (by decide) (by decide) with
                  ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                ·
                  linarith only [hlam, hc012xy, hc789yz, htr016a, htr023a, htr168a, htr237a, htr379a, htr689a]
                ·
                  linarith only [hlam, hc012xy, hc568yz, htr018a, htr024a, htr189a, htr245a, htr458a, htr689a]
            ·
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd34b, hd78a, htr134a, htr135a, htr345b, htr457a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hd12b, hd57a, htr123a, htr237a, htr378a, htr578a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc347yx, htr134a, htr137c, htr178a, htr378a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd34b, hd79a, htr134a, htr135a, htr345b, htr457a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hd12b, hd57a, htr123a, htr237a, htr379a, htr579a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc347yx, htr134a, htr137c, htr179a, htr379a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc012xy, hc567yz, htr017a, htr024a, htr178a, htr245a, htr457a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                linarith only [hlam, hc012xy, hc578yz, htr016a, htr023a, htr167a, htr235a, htr358a, htr678a])
              obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc012xy, hc567yz, htr017a, htr024a, htr179a, htr245a, htr457a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hc012xy, hc789zy, htr016a, htr023a, htr167a, htr238a, htr389a, htr679a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568xy, htr345b, htr358b, htr389a, htr456a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd01a, hd89b, htr016a, htr167a, htr678a, htr789a]
              ·
                linarith only [hlam, hd56a, hd78b, htr345b, htr358a, htr456a, htr589a, htr789a]

theorem shard_153 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr348b : m.d 4 8 < m.d 3 8)
    : False :=
  proof_shard_153 m htr013c htr015a htr015c htr016a htr017a htr018a htr023a htr023b htr024a htr025b htr026b htr027a htr027b htr035c htr045b htr046b htr123a htr123b htr124a htr134a htr135a htr135c htr145b htr146b htr235a htr235b htr236a htr236b htr245a htr246a htr247a htr345b htr346b htr347b htr348b

#print axioms shard_153
end Jsp404.NoSatElevenDBMTerminal
