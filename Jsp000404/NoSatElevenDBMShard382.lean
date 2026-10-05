import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_382 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr037c : m.d 0 7 < m.d 3 7)
    (htr038c : m.d 0 8 < m.d 3 8)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr048b : m.d 4 8 < m.d 0 8)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr147b : m.d 4 7 < m.d 1 7)
    (htr148b : m.d 4 8 < m.d 1 8)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd14a, hd14braw⟩ := m.hrange 1 4 (by decide)
  have hd14b : m.d 1 4 < 4*lam := by
    linarith only [hd14braw, hp]
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
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
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
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
  rcases m.htr 2 3 6 (by decide) (by decide) with
    ⟨htr236a, htr236b, htr236c, _, _⟩ | ⟨htr236a, htr236b, htr236c, _, _⟩
  ·
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, htr235c, htr236b, htr256c])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, htr235b, htr256a, htr356a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hc567yx, htr235a, htr236a, htr356c, htr357a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr358a, htr358b, htr358c, _, _⟩
      linarith only [hlam, hc568yx, htr235a, htr236a, htr356c, htr358a])
    obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd13a, hd67b, htr135a, htr235a, htr236a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hd13a, hd68b, htr135a, htr235a, htr236a, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    rcases m.htr 4 6 7 (by decide) (by decide) with
      ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
    ·
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc346zy, htr236a, htr237a, htr367b, htr467a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd13a, hd78b, htr135a, htr235a, htr237a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hd13a, hd79b, htr135a, htr235a, htr237a, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc346zy, htr367c, htr378a, htr467a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc346zy, htr147b, htr178a, htr367a, htr467b, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc134xy, hc378zy, htr014a, htr017a, htr135a, htr178a, htr235a, htr238a])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc346zy, htr367c, htr379a, htr467a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc346zy, htr147b, htr179a, htr367a, htr467b, htr679a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc134xy, hc789yz, htr014a, htr017a, htr135a, htr179a, htr358a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc134xy, hc578zy, htr014a, htr017a, htr138a, htr178a, htr389a, htr589a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd34b, hd78a, htr234a, htr238a, htr389a, htr789a]
      ·
        linarith only [hlam, hd14b, hd89a, htr014a, htr017a, htr178a, htr789a]
    ·
      have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr237a, htr237b, htr237c, _, _⟩
        linarith only [hlam, hc134xy, hc367zy, htr014a, htr016a, htr135a, htr146b, htr235a, htr237a, htr467a])
      obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd14b, hd78a, htr014a, htr016a, htr146b, htr467a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr378a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc134xy, hc567zy, htr014a, htr016a, htr137a, htr146b, htr378a, htr467a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc134xy, hc678yz, htr014a, htr016a, htr135a, htr168a, htr357a, htr578a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc134xy, hc789yx, htr014a, htr017a, htr135a, htr179a, htr357a, htr578a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc136yz, htr168a, htr236a, htr238a, htr368b])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hc123yz, htr137b, htr179a, htr237a, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd13a, hd89b, htr135a, htr235a, htr238a, htr389a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc134xy, hc567zy, htr014a, htr016a, htr137a, htr146b, htr379a, htr467a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc134xy, hc789zy, htr014a, htr018a, htr135a, htr189a, htr357a, htr579a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc136yz, htr168a, htr368c, htr389a, htr689a]
      ·
        linarith only [hlam, hc136yz, htr168b, htr189a, htr368a, htr689a]
  ·
    rcases m.htr 2 3 7 (by decide) (by decide) with
      ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
    ·
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr235c, htr237b, htr257c])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, htr236c, htr237b, htr267c])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr235b, htr257a, htr357a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr356a, htr356b, htr356c, _, _⟩
        linarith only [hlam, hc567xy, htr235a, htr237a, htr356a, htr357c])
      obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, htr236b, htr267a, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc678yx, htr236a, htr237a, htr367c, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hc679yx, htr236a, htr237a, htr367c, htr369a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd13a, hd78b, htr135a, htr235a, htr237a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hd13a, hd56b, htr135a, htr235a, htr237a, htr367c, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hd13a, hd67b, htr136a, htr368a, htr567a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc134xy, hc678zy, htr014a, htr017a, htr135a, htr178a, htr356a, htr568a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc137yz, htr178a, htr237a, htr238a, htr378b])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd13a, hd89b, htr135a, htr235a, htr238a, htr389a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hd13a, hd67b, htr136a, htr369a, htr567a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc134xy, hc689zy, htr014a, htr018a, htr135a, htr189a, htr356a, htr569a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc137yz, htr178a, htr378c, htr389a, htr789a]
      ·
        linarith only [hlam, hc137yz, htr178b, htr189a, htr378a, htr789a]
    ·
      rcases m.htr 2 3 8 (by decide) (by decide) with
        ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, htr235c, htr238b, htr258c])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
          linarith only [hlam, htr236c, htr238b, htr268c])
        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr237c, htr238b, htr278c])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr235b, htr258a, htr358a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr356a, htr356b, htr356c, _, _⟩
          linarith only [hlam, hc568xy, htr235a, htr238a, htr356a, htr358c])
        obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, htr236b, htr268a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc678xy, htr236a, htr238a, htr367a, htr368c])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, htr237b, htr278a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd13a, hd56b, htr135a, htr235a, htr238a, htr368c, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd13a, hd68b, htr136a, htr367a, htr567a, htr568a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hd13a, hd78b, htr135a, htr356a, htr567a, htr678a]
        ·
          linarith only [hlam, hd13a, hd67b, htr135a, htr235a, htr238a, htr378c, htr678a]
      ·
        rcases m.htr 2 3 9 (by decide) (by decide) with
          ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
        ·
          have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr259a, htr259b, htr259c, _, _⟩
            linarith only [hlam, htr235c, htr239b, htr259c])
          obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
          have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr269a, htr269b, htr269c, _, _⟩
            linarith only [hlam, htr236c, htr239b, htr269c])
          obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, htr237c, htr239b, htr279c])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr359a, htr359b, htr359c, _, _⟩
            linarith only [hlam, htr235b, htr259a, htr359a])
          obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
          have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr356a, htr356b, htr356c, _, _⟩
            linarith only [hlam, hc569xy, htr235a, htr239a, htr356a, htr359c])
          obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, htr236b, htr269a, htr369a])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc679xy, htr236a, htr239a, htr367a, htr369c])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, htr237b, htr279a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hd13a, hd56b, htr135a, htr235a, htr239a, htr369c, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hd13a, hd69b, htr136a, htr367a, htr567a, htr569a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd13a, hd79b, htr135a, htr356a, htr567a, htr679a]
          ·
            linarith only [hlam, hd13a, hd67b, htr135a, htr235a, htr239a, htr379c, htr679a]
        ·
          rcases m.htr 2 3 10 (by decide) (by decide) with
            ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
          ·
            have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
              linarith only [hlam, htr2310b, htr235c, htr2510c])
            obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
            have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
              linarith only [hlam, htr2310b, htr236c, htr2610c])
            obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, htr2310b, htr237c, htr2710c])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
              linarith only [hlam, htr235b, htr2510a, htr3510a])
            obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
            have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr356a, htr356b, htr356c, _, _⟩
              linarith only [hlam, hc5610xy, htr2310a, htr235a, htr3510c, htr356a])
            obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
            have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              linarith only [hlam, htr236b, htr2610a, htr3610a])
            obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc6710xy, htr2310a, htr236a, htr3610c, htr367a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
              linarith only [hlam, htr237b, htr2710a, htr3710a])
            obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              linarith only [hlam, hd13a, hd56b, htr135a, htr2310a, htr235a, htr3610c, htr5610a])
            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd13a, hd610b, htr136a, htr367a, htr5610a, htr567a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd13a, hd710b, htr135a, htr356a, htr567a, htr6710a]
            ·
              linarith only [hlam, hd13a, hd67b, htr135a, htr2310a, htr235a, htr3710c, htr6710a]
          ·
            rcases m.htr 3 5 6 (by decide) (by decide) with
              ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
            ·
              have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                linarith only [hlam, htr035c, htr056a, htr356a])
              obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, htr135c, htr156a, htr356a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hc123yz, htr135a, htr235c, htr256a, htr356a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              rcases m.htr 3 5 7 (by decide) (by decide) with
                ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
              ·
                rcases m.htr 3 6 7 (by decide) (by decide) with
                  ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
                ·
                  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                    linarith only [hlam, htr036c, htr067a, htr367a])
                  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                    linarith only [hlam, htr136c, htr167a, htr367a])
                  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                    linarith only [hlam, hc123yz, htr136a, htr236c, htr267a, htr367a])
                  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                  rcases m.htr 5 6 7 (by decide) (by decide) with
                    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                  ·
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc134xy, hc678yx, htr014a, htr016a, htr135a, htr168a, htr356a, htr567a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                      linarith only [hlam, hc134xy, hc679yx, htr014a, htr016a, htr135a, htr169a, htr356a, htr567a])
                    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                      linarith only [hlam, hc123yz, htr136b, htr168a, htr236a, htr368a])
                    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                      linarith only [hlam, hc123yz, htr136b, htr169a, htr236a, htr369a])
                    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hd13a, hd67b, htr136a, htr368a, htr567a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc134xy, hc678zy, htr014a, htr017a, htr135a, htr178a, htr356a, htr568a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc123yz, htr137b, htr178a, htr237a, htr378a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hd13a, hd67b, htr136a, htr369a, htr567a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc134xy, hc689zy, htr014a, htr018a, htr135a, htr189a, htr356a, htr569a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd13a, hd78b, htr135a, htr356a, htr567a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd13a, hd89b, htr135a, htr356a, htr568a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd13a, hd68b, htr137a, htr378a, htr689a, htr789a]
                    ·
                      linarith only [hlam, hc167yz, htr178b, htr189a, htr678a, htr789a]
                  ·
                    have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                      linarith only [hlam, hc568yx, htr256b, htr258a, htr267a, htr567a])
                    obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hd13a, hd68b, htr136a, htr367a, htr567a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    rcases m.htr 4 6 8 (by decide) (by decide) with
                      ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                    ·
                      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                        linarith only [hlam, hc456yz, htr036c, htr068a, htr367a, htr468a, htr567a])
                      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                        linarith only [hlam, hc456yz, htr267a, htr268a, htr468a, htr567a])
                      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                      rcases m.htr 4 6 9 (by decide) (by decide) with
                        ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                      ·
                        rcases m.htr 4 6 10 (by decide) (by decide) with
                          ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                        ·
                          rcases m.htr 6 7 8 (by decide) (by decide) with
                            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                          ·
                            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                              linarith only [hlam, hc134xy, hc789yx, htr014a, htr017a, htr136a, htr179a, htr367a, htr678a])
                            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                            have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                              linarith only [hlam, hc156yz, htr167b, htr179a, htr267c, htr279a, htr567a])
                            obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                              linarith only [hlam, hd13a, hd57b, htr136a, htr367a, htr578a, htr678a])
                            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                              linarith only [hlam, hd12a, hd78b, htr127a, htr279a, htr578a, htr579a])
                            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                              linarith only [hlam, hc134xy, hc789zy, htr014a, htr018a, htr135a, htr189a, htr357a, htr579a])
                            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                              linarith only [hlam, hc456yz, htr148b, htr189a, htr468b, htr568a, htr689a])
                            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                            rcases m.htr 7 8 9 (by decide) (by decide) with
                              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                            ·
                              linarith only [hlam, hd13a, hd89b, htr136a, htr367a, htr678a, htr789a]
                            ·
                              linarith only [hlam, hd12a, hd78b, htr126a, htr268a, htr689a, htr789a]
                          ·
                            have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                              linarith only [hlam, hc056yz, htr067b, htr078a, htr567a, htr678a])
                            obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc156yz, htr167b, htr178a, htr567a, htr678a])
                            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                              linarith only [hlam, hc134xy, hc789xy, htr014a, htr017a, htr136a, htr178a, htr367a, htr679a])
                            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                              linarith only [hlam, hc056yz, htr067b, htr079a, htr567a, htr679a])
                            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                              linarith only [hlam, hd34b, hd78a, htr037c, htr079a, htr178a, htr179a, htr234a, htr237a])
                            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                              linarith only [hlam, hc124xy, hc789yz, htr014a, htr017a, htr125a, htr179a, htr258a, htr589a])
                            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                            have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                              linarith only [hlam, hc124xy, hc578zy, htr014a, htr017a, htr128a, htr178a, htr289a, htr589a])
                            obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                              linarith only [hlam, hc456yz, htr048b, htr089a, htr268c, htr289a, htr468b, htr568a])
                            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                            rcases m.htr 7 8 9 (by decide) (by decide) with
                              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                            ·
                              linarith only [hlam, hd34b, hd78a, htr038c, htr089a, htr234a, htr238a, htr789a]
                            ·
                              linarith only [hlam, hd34b, hd89a, htr037c, htr078a, htr234a, htr237a, htr789a]
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
                          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                            linarith only [hlam, hd34b, hd610a, htr037c, htr0710a, htr146b, htr167b, htr1710a, htr234a, htr237a, htr4610a])
                          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                            linarith only [hlam, hc134xy, hc7810yx, htr014a, htr017a, htr136a, htr1710a, htr367a, htr678a])
                          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                            linarith only [hlam, hc056yz, htr067b, htr078a, htr567a, htr678a])
                          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                          rcases m.htr 7 8 10 (by decide) (by decide) with
                            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          ·
                            linarith only [hlam, hd34b, hd78a, htr038c, htr0810a, htr234a, htr238a, htr7810a]
                          ·
                            linarith only [hlam, hd34b, hd810a, htr037c, htr078a, htr234a, htr237a, htr7810a]
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
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hd34b, hd69a, htr037c, htr079a, htr146b, htr167b, htr179a, htr234a, htr237a, htr469a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hc134xy, hc789yx, htr014a, htr017a, htr136a, htr179a, htr367a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                          linarith only [hlam, hc056yz, htr067b, htr078a, htr567a, htr678a])
                        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd34b, hd78a, htr038c, htr089a, htr234a, htr238a, htr789a]
                        ·
                          linarith only [hlam, hd34b, hd89a, htr037c, htr078a, htr234a, htr237a, htr789a]
                    ·
                      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                        linarith only [hlam, htr046b, htr068a, htr468a])
                      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, htr067b, htr068c, htr078b])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                        linarith only [hlam, hd34b, hd68a, htr037c, htr078a, htr146b, htr167b, htr178a, htr234a, htr237a, htr468a])
                      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                        linarith only [hlam, htr126c, htr146b, htr268a, htr468a])
                      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                        linarith only [hlam, hc134xy, hc789xy, htr014a, htr017a, htr136a, htr178a, htr367a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                        linarith only [hlam, hc056yz, htr067b, htr079a, htr567a, htr679a])
                      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                        linarith only [hlam, hd34b, hd68a, htr037c, htr079a, htr146b, htr167b, htr179a, htr234a, htr237a, htr468a])
                      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc124xy, hc789yz, htr014a, htr017a, htr125a, htr179a, htr258a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                        linarith only [hlam, hc124xy, hc568zy, htr014a, htr016a, htr128a, htr146b, htr289a, htr468a, htr589a])
                      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd56b, hd78a, htr267a, htr268c, htr289a, htr567a, htr789a]
                      ·
                        linarith only [hlam, hd34b, hd89a, htr037c, htr078a, htr234a, htr237a, htr789a]
                ·
                  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                    linarith only [hlam, hc123yz, htr136b, htr167a, htr236a, htr367a])
                  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                    linarith only [hlam, htr236b, htr267a, htr367a])
                  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd34b, hd78a, htr234a, htr236a, htr367a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                    linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr378a, htr678a])
                  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc134xy, hc567zy, htr014a, htr016a, htr137a, htr167a, htr378a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, hc134xy, hc678yz, htr014a, htr016a, htr135a, htr168a, htr357a, htr578a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc134xy, hc789yx, htr014a, htr017a, htr135a, htr179a, htr357a, htr578a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                    linarith only [hlam, hd34b, hd67a, htr167a, htr168a, htr234a, htr236c, htr268a])
                  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc147yx, hc678xy, htr014a, htr016a, htr167a, htr179a, htr267c, htr268a, htr279a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc124xy, hc567zy, htr014a, htr016a, htr127a, htr167a, htr279a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc134xy, hc789zy, htr014a, htr018a, htr135a, htr189a, htr357a, htr579a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc678xy, htr167a, htr168b, htr189a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd13a, hd89b, htr135a, htr357a, htr578a, htr789a]
                  ·
                    linarith only [hlam, hd67a, hd78b, htr167a, htr168a, htr689a, htr789a]
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hc023yz, htr035b, htr057a, htr235a, htr357a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                  linarith only [hlam, htr056b, htr057c, htr067b])
                obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                  linarith only [hlam, hc123yz, htr135b, htr157a, htr235a, htr357a])
                obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hd34b, hd57a, htr036c, htr067a, htr156b, htr157a, htr167a, htr234a, htr236a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, htr235b, htr257a, htr357a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc134xy, hc678xy, htr014a, htr016a, htr135a, htr167a, htr356a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                  linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
                obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hd34b, hd57a, htr036c, htr068a, htr156b, htr157a, htr168a, htr234a, htr236a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hc134xy, hc679xy, htr014a, htr016a, htr135a, htr167a, htr356a, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hc567yx, htr056b, htr057a, htr069a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                  linarith only [hlam, hd34b, hd57a, htr036c, htr069a, htr156b, htr157a, htr169a, htr234a, htr236a])
                obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd34b, hd78a, htr234a, htr235a, htr357a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc567yx, htr256a, htr257c, htr278a, htr578a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd34b, hd89a, htr036c, htr068a, htr234a, htr236a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hd34b, hd68a, htr234a, htr238a, htr389a, htr689a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hc124xy, hc689yz, htr014a, htr016a, htr127a, htr169a, htr278a, htr789a]
                ·
                  linarith only [hlam, hc134xy, hc678yz, htr014a, htr016a, htr138a, htr168a, htr389a, htr789a]
            ·
              have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                linarith only [hlam, hc123yz, htr135b, htr156a, htr235a, htr356a])
              obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
              have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr456a, htr456b, htr456c, _, _⟩
                linarith only [hlam, hd34b, hd45a, htr234a, htr235a, htr356a, htr456a])
              obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd34b, hd67a, htr234a, htr235a, htr356a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr234a, htr236a, htr367a, htr567a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd34b, hd68a, htr234a, htr235a, htr356a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr234a, htr236a, htr368a, htr568a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                  linarith only [hlam, hd34b, hd56a, htr035c, htr057a, htr234a, htr235a, htr456a, htr457a])
                obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hd34b, hd56a, htr234a, htr235c, htr257a, htr456a, htr457a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                rcases m.htr 4 5 8 (by decide) (by decide) with
                  ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
                ·
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hd34b, hd56a, htr035c, htr058a, htr234a, htr235a, htr456a, htr458a])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, hc567xy, htr257a, htr258a, htr456a, htr458a])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
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
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc124xy, hc789yx, htr014a, htr017a, htr125a, htr179a, htr257a, htr578a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hc567xy, htr147b, htr179a, htr456a, htr457b, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc124xy, hc789zy, htr014a, htr018a, htr125a, htr189a, htr257a, htr579a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc568xy, htr148b, htr189a, htr456a, htr458b, htr589a])
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
                          linarith only [hlam, hc124xy, hc789xy, htr014a, htr017a, htr125a, htr147b, htr257a, htr478a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, hc567xy, htr047b, htr079a, htr456a, htr457b, htr579a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hd34b, hd56a, htr037c, htr079a, htr147b, htr179a, htr234a, htr237a, htr456a, htr457b])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc124xy, hc789yz, htr014a, htr017a, htr125a, htr179a, htr258a, htr589a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, hc568xy, htr048b, htr089a, htr456a, htr458b, htr589a])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd34b, hd78a, htr038c, htr089a, htr234a, htr238a, htr789a]
                        ·
                          linarith only [hlam, hd14b, hd89a, htr014a, htr017a, htr147b, htr478a, htr789a]
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
                      have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                        linarith only [hlam, hd34b, hd56a, htr037c, htr0710a, htr147b, htr1710a, htr234a, htr237a, htr456a, htr457b])
                      obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc124xy, hc7810yx, htr014a, htr017a, htr125a, htr1710a, htr257a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, hc567xy, htr047b, htr078a, htr456a, htr457b, htr578a])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      rcases m.htr 7 8 10 (by decide) (by decide) with
                        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      ·
                        linarith only [hlam, hd34b, hd78a, htr038c, htr0810a, htr234a, htr238a, htr7810a]
                      ·
                        linarith only [hlam, hd34b, hd810a, htr037c, htr078a, htr234a, htr237a, htr7810a]
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
                    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                      linarith only [hlam, hd34b, hd56a, htr037c, htr079a, htr147b, htr179a, htr234a, htr237a, htr456a, htr457b])
                    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                      linarith only [hlam, hc124xy, hc789yx, htr014a, htr017a, htr125a, htr179a, htr257a, htr578a])
                    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                      linarith only [hlam, hc567xy, htr047b, htr078a, htr456a, htr457b, htr578a])
                    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd34b, hd78a, htr038c, htr089a, htr234a, htr238a, htr789a]
                    ·
                      linarith only [hlam, hd34b, hd89a, htr037c, htr078a, htr234a, htr237a, htr789a]
                ·
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, htr045b, htr058a, htr458a])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, htr057b, htr058c, htr078b])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hd34b, hd56a, htr037c, htr078a, htr147b, htr178a, htr234a, htr237a, htr456a, htr457b])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
                    linarith only [hlam, htr025c, htr045b, htr258a, htr458a])
                  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc124xy, hc789xy, htr014a, htr017a, htr125a, htr178a, htr257a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, hc567xy, htr047b, htr079a, htr456a, htr457b, htr579a])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hd34b, hd56a, htr037c, htr079a, htr147b, htr179a, htr234a, htr237a, htr456a, htr457b])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd14b, hd89a, htr014a, htr015a, htr145b, htr458a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc578yx, htr257a, htr258c, htr289a, htr589a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  rcases m.htr 6 8 9 (by decide) (by decide) with
                    ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                  ·
                    linarith only [hlam, hc134xy, hc789yz, htr014a, htr017a, htr136a, htr179a, htr368a, htr689a]
                  ·
                    linarith only [hlam, hc124xy, hc568yz, htr014a, htr015a, htr128a, htr145b, htr289a, htr458a, htr689a]
              ·
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd14b, hd78a, htr014a, htr015a, htr145b, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr378a, htr578a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd14b, hd79a, htr014a, htr015a, htr145b, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr379a, htr579a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc134xy, hc567yz, htr014a, htr015a, htr137a, htr145b, htr378a, htr457a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                  linarith only [hlam, hc134xy, hc578yz, htr014a, htr015a, htr136a, htr158a, htr367a, htr678a])
                obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc134xy, hc567yz, htr014a, htr015a, htr137a, htr145b, htr379a, htr457a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc134xy, hc789zy, htr014a, htr018a, htr136a, htr189a, htr367a, htr679a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc568xy, htr156a, htr158b, htr189a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd13a, hd89b, htr136a, htr367a, htr678a, htr789a]
                ·
                  linarith only [hlam, hd56a, hd78b, htr156a, htr158a, htr589a, htr789a]

theorem shard_382 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr037c : m.d 0 7 < m.d 3 7)
    (htr038c : m.d 0 8 < m.d 3 8)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr048b : m.d 4 8 < m.d 0 8)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    (htr138a : m.d 1 3 + lam ≤ m.d 3 8)
    (htr145b : m.d 4 5 < m.d 1 5)
    (htr146b : m.d 4 6 < m.d 1 6)
    (htr147b : m.d 4 7 < m.d 1 7)
    (htr148b : m.d 4 8 < m.d 1 8)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 2 3)
    : False :=
  proof_shard_382 m htr014a htr015a htr016a htr017a htr018a htr025c htr035b htr035c htr036c htr037c htr038c htr045b htr046b htr047b htr048b htr125a htr126a htr126c htr127a htr128a htr135a htr135b htr135c htr136a htr136b htr136c htr137a htr137b htr138a htr145b htr146b htr147b htr148b htr234a htr235a htr235b htr235c

#print axioms shard_382
end Jsp404.NoSatElevenDBMTerminal
