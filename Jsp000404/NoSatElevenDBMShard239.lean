import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_239 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr037b : m.d 3 7 < m.d 0 7)
    (htr038b : m.d 3 8 < m.d 0 8)
    (htr039b : m.d 3 9 < m.d 0 9)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr138b : m.d 3 8 < m.d 1 8)
    (htr138c : m.d 1 8 < m.d 1 3)
    (htr139a : m.d 3 9 + lam ≤ m.d 1 3)
    (htr139b : m.d 3 9 < m.d 1 9)
    (htr156a : m.d 1 5 + lam ≤ m.d 5 6)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr158a : m.d 1 5 + lam ≤ m.d 5 8)
    (htr159a : m.d 1 5 + lam ≤ m.d 5 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr349a : m.d 4 9 + lam ≤ m.d 3 4)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd15a := (m.hrange 1 5 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd48a := (m.hrange 4 8 (by decide)).1
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
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc036xy, hc036yx, hc036yz, hc036zy⟩ := endpoint_caps m 0 3 6 (by decide) (by decide)
  obtain ⟨hc047xy, hc047yx, hc047yz, hc047zy⟩ := endpoint_caps m 0 4 7 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc158xy, hc158yx, hc158yz, hc158zy⟩ := endpoint_caps m 1 5 8 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc368xy, hc368yx, hc368yz, hc368zy⟩ := endpoint_caps m 3 6 8 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc379xy, hc379yx, hc379yz, hc379zy⟩ := endpoint_caps m 3 7 9 (by decide) (by decide)
  obtain ⟨hc389xy, hc389yx, hc389yz, hc389zy⟩ := endpoint_caps m 3 8 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc479xy, hc479yx, hc479yz, hc479zy⟩ := endpoint_caps m 4 7 9 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd13b, hd67a, htr134a, htr234a, htr236a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc346yx, htr234a, htr236c, htr267a, htr367a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd13b, hd68a, htr134a, htr234a, htr236a, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hd13b, hd69a, htr134a, htr234a, htr236a, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr017a, htr017b, htr017c, _, _⟩
      linarith only [hlam, hc123zy, htr013a, htr017a, htr137b, htr237a])
    obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc036zy, htr067a, htr236a, htr237a, htr367c])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc136zy, htr167a, htr236a, htr237a, htr367c])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hc356yz, htr236a, htr237a, htr367c, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    rcases m.htr 0 1 6 (by decide) (by decide) with
      ⟨htr016a, htr016b, htr016c, _, _⟩ | ⟨htr016a, htr016b, htr016c, _, _⟩
    ·
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd15a, hd78b, htr015a, htr016a, htr156c, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd35a, hd67b, htr235a, htr237a, htr378a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc135yx, hc467yz, htr015a, htr016a, htr137a, htr167a, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc135yx, hc678zy, htr015a, htr016a, htr134a, htr168a, htr347a, htr478a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr018a, htr018b, htr018c, _, _⟩
        linarith only [hlam, hc136zy, htr016a, htr018a, htr168b, htr368a])
      obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc135yx, hc789xy, htr015a, htr017a, htr134a, htr179a, htr347a, htr478a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr238a, htr238b, htr238c, _, _⟩
        linarith only [hlam, hc136zy, htr168a, htr236a, htr238a, htr368c])
      obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hc123zy, htr137c, htr179a, htr237a, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd13b, hd89a, htr134a, htr234a, htr238a, htr389a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc135yx, hc467yz, htr015a, htr016a, htr137a, htr167a, htr379a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc135yx, hc789yz, htr015a, htr018a, htr134a, htr189a, htr347a, htr479a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc136zy, htr168c, htr189a, htr368a, htr689a]
      ·
        linarith only [hlam, hc136zy, htr168a, htr368b, htr389a, htr689a]
    ·
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hd12b, hd36a, htr012a, htr016a, htr168a, htr368a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hd12b, hd36a, htr012a, htr016a, htr169a, htr369a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc126yx, htr012a, htr016c, htr069a, htr169a])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      rcases m.htr 2 3 8 (by decide) (by decide) with
        ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
      ·
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc123zy, htr013a, htr018a, htr138b, htr238a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        rcases m.htr 2 3 9 (by decide) (by decide) with
          ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
        ·
          have hforced019 := (m.htr 0 1 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr019a, htr019b, htr019c, _, _⟩
            linarith only [hlam, hc123zy, htr013a, htr019a, htr139b, htr239a])
          obtain ⟨htr019a, htr019b, htr019c, _, _⟩ := hforced019
          rcases m.htr 2 3 10 (by decide) (by decide) with
            ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
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
                linarith only [hlam, hd35a, hd89b, htr235a, htr237a, htr378a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                linarith only [hlam, hd35a, hd78b, htr235a, htr238a, htr389a, htr789a])
              obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc135yx, hc478yz, htr015a, htr017a, htr138a, htr178a, htr389a, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc135yx, hc789zy, htr015a, htr017a, htr134a, htr179a, htr348a, htr489a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc135yx, hc8910xy, htr015a, htr018a, htr134a, htr1810a, htr348a, htr489a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hd35a, hd78b, htr178a, htr179a, htr235a, htr237b, htr279a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                linarith only [hlam, hc158xy, hc789yx, htr015a, htr017a, htr178a, htr1810a, htr278b, htr279a, htr2810a])
              obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hc125yx, hc478yz, htr015a, htr017a, htr128a, htr178a, htr2810a, htr4810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc135yx, hc8910yz, htr015a, htr019a, htr134a, htr1910a, htr348a, htr4810a])
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
                linarith only [hlam, hd13b, hd910a, htr134a, htr348a, htr489a, htr8910a]
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
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hd13b, hd79a, htr137a, htr378a, htr478a, htr479a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
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
                    linarith only [hlam, hd35a, hd79b, htr038b, htr089a, htr167c, htr178c, htr189a, htr235a, htr238a, htr679a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, htr267c, htr279a, htr679a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    linarith only [hlam, hc135yx, hc8910yx, htr015a, htr018a, htr137a, htr189a, htr378a, htr7810a])
                  obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                    linarith only [hlam, hc047zy, htr078c, htr0810a, htr478a, htr7810a])
                  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                  have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                    linarith only [hlam, hd35a, hd79b, htr038b, htr0810a, htr167c, htr178c, htr1810a, htr235a, htr238a, htr679a])
                  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc135yx, hc8910zy, htr015a, htr018a, htr134a, htr1810a, htr349a, htr4910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                    linarith only [hlam, hc125yx, hc479yz, htr015a, htr017a, htr129a, htr167c, htr2910a, htr4910a, htr679a])
                  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd35a, hd910b, htr038b, htr089a, htr235a, htr238a, htr8910a]
                  ·
                    linarith only [hlam, hd47a, hd89b, htr278a, htr279b, htr2910a, htr478a, htr8910a]
                ·
                  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                    linarith only [hlam, hc467yz, htr037b, htr079a, htr378a, htr478a, htr679a])
                  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc467yz, htr278a, htr279a, htr478a, htr679a])
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
                      linarith only [hlam, hd35a, hd710b, htr038b, htr0810a, htr167c, htr178c, htr1810a, htr235a, htr238a, htr6710a])
                    obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hc135yx, hc8910xy, htr015a, htr018a, htr137a, htr1810a, htr378a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, hc047zy, htr078c, htr089a, htr478a, htr789a])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd35a, hd910b, htr038b, htr089a, htr235a, htr238a, htr8910a]
                    ·
                      linarith only [hlam, hd35a, hd89b, htr039b, htr0910a, htr235a, htr239a, htr8910a]
                  ·
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, hc047zy, htr078c, htr089a, htr478a, htr789a])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                        linarith only [hlam, hc147zy, htr178c, htr189a, htr478a, htr789a])
                      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                        linarith only [hlam, hc135yx, hc8910yx, htr015a, htr018a, htr137a, htr189a, htr378a, htr7810a])
                      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                      have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                        linarith only [hlam, hc047zy, htr078c, htr0810a, htr478a, htr7810a])
                      obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                        linarith only [hlam, hd35a, hd89b, htr038b, htr0810a, htr1810a, htr189a, htr235a, htr238a])
                      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                        linarith only [hlam, hc135yx, hc8910zy, htr015a, htr018a, htr134a, htr1810a, htr349a, htr4910a])
                      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                      have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                        linarith only [hlam, hc125yx, hc489yz, htr015a, htr018a, htr129a, htr189a, htr2910a, htr4910a])
                      obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                      have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                        linarith only [hlam, hc467yz, htr069c, htr0910a, htr279b, htr2910a, htr479a, htr679c])
                      obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd35a, hd910b, htr038b, htr089a, htr235a, htr238a, htr8910a]
                      ·
                        linarith only [hlam, hd35a, hd89b, htr039b, htr0910a, htr235a, htr239a, htr8910a]
                    ·
                      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                        linarith only [hlam, hc135yx, hc8910xy, htr015a, htr018a, htr137a, htr1810a, htr378a, htr789a])
                      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                        linarith only [hlam, hc147zy, htr178c, htr1810a, htr278b, htr2810a, htr478a])
                      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hd13b, hd48a, htr137a, htr378a, htr489a, htr789a])
                      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                        linarith only [hlam, hd12b, hd89a, htr128a, htr2810a, htr4810a, htr489a])
                      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                        linarith only [hlam, hc135yx, hc8910yz, htr015a, htr019a, htr134a, htr1910a, htr348a, htr4810a])
                      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                        linarith only [hlam, hc467yz, htr169c, htr1910a, htr479a, htr679c, htr7910a])
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
                  linarith only [hlam, hc135yx, hc789xy, htr015a, htr017a, htr134a, htr179a, htr347a, htr478a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                  linarith only [hlam, hc135yx, hc7810xy, htr015a, htr017a, htr134a, htr1710a, htr347a, htr478a])
                obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hc123zy, htr137c, htr179a, htr237a, htr379a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                  linarith only [hlam, hc123zy, htr137c, htr1710a, htr237a, htr3710a])
                obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hd13b, hd78a, htr137a, htr379a, htr478a, htr479a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc135yx, hc789yz, htr015a, htr018a, htr134a, htr189a, htr347a, htr479a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                  linarith only [hlam, hc123zy, htr138c, htr189a, htr238a, htr389a])
                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                  linarith only [hlam, hd13b, hd78a, htr137a, htr3710a, htr4710a, htr478a])
                obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                  linarith only [hlam, hc135yx, hc7910yz, htr015a, htr019a, htr134a, htr1910a, htr347a, htr4710a])
                obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd13b, hd89a, htr134a, htr347a, htr478a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hd13b, hd910a, htr134a, htr347a, htr479a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hc178zy, htr189c, htr1910a, htr789a, htr8910a]
                ·
                  linarith only [hlam, hd13b, hd79a, htr138a, htr389a, htr7910a, htr8910a]
          ·
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, htr2310c, htr237b, htr2710b])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
              linarith only [hlam, htr2310c, htr238b, htr2810b])
            obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
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
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hd13b, hd47a, htr134a, htr2310a, htr234a, htr3710b, htr4710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hd13b, hd710a, htr137a, htr378a, htr4710a, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            rcases m.htr 7 8 10 (by decide) (by decide) with
              ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            ·
              linarith only [hlam, hd13b, hd78a, htr134a, htr2310a, htr234a, htr3810b, htr7810a]
            ·
              linarith only [hlam, hd13b, hd810a, htr134a, htr347a, htr478a, htr7810a]
        ·
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, htr237b, htr239c, htr279b])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
            linarith only [hlam, htr238b, htr239c, htr289b])
          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
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
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd13b, hd47a, htr134a, htr234a, htr239a, htr379b, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd13b, hd79a, htr137a, htr378a, htr478a, htr479a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd13b, hd78a, htr134a, htr234a, htr239a, htr389b, htr789a]
          ·
            linarith only [hlam, hd13b, hd89a, htr134a, htr347a, htr478a, htr789a]
      ·
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, htr237b, htr238c, htr278b])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
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
          linarith only [hlam, hd13b, hd89a, htr134a, htr234a, htr238a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd13b, hd47a, htr134a, htr234a, htr238a, htr378b, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd13b, hd78a, htr137a, htr379a, htr478a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hd13b, hd78a, htr137a, htr3710a, htr4710a, htr478a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, htr378b, htr389a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd13b, hd910a, htr134a, htr347a, htr479a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc136yx, hc368yz, htr134a, htr169a, htr234a, htr238a, htr568a, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc135yx, hc789yz, htr134a, htr156a, htr347a, htr479a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc135yx, hc7910yz, htr134a, htr156a, htr347a, htr4710a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc368yz, htr389a, htr689c, htr6910a, htr8910a]
          ·
            linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
        ·
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc136yx, hc679zy, htr134a, htr168a, htr347a, htr479a, htr568a, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc356yz, htr368b, htr389a, htr568a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd67b, hd79a, htr567a, htr569a, htr6910a, htr7910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc136yx, hc7910yz, htr134a, htr168a, htr347a, htr4710a, htr689a, htr8910a]
          ·
            linarith only [hlam, hc136yx, hc789yz, htr134a, htr169a, htr347a, htr479a, htr6910a, htr8910a]
  ·
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd13b, hd78a, htr134a, htr234a, htr237a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd13b, hd79a, htr134a, htr234a, htr237a, htr379a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr016a, htr016b, htr016c, _, _⟩
        linarith only [hlam, hc135yx, hc367yz, htr015a, htr016a, htr134a, htr156c, htr234a, htr237a, htr567a])
      obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hd12b, hd36a, htr012a, htr016a, htr168a, htr368a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hd12b, hd36a, htr012a, htr016a, htr169a, htr369a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc136yx, hc367yz, htr134a, htr168a, htr234a, htr237a, htr567a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc136yx, hc367yz, htr134a, htr169a, htr234a, htr237a, htr567a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc135yx, hc378yz, htr134a, htr156a, htr234a, htr238a, htr567a, htr678a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr018a, htr018b, htr018c, _, _⟩
          linarith only [hlam, hc123zy, htr013a, htr018a, htr138b, htr238a])
        obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd35a, hd89b, htr356a, htr567a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd35a, hd78b, htr235a, htr238a, htr389a, htr789a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc135yx, hc478yz, htr138a, htr156a, htr389a, htr489a, htr567a, htr678a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc135yx, hc8910xy, htr015a, htr018a, htr134a, htr1810a, htr348a, htr489a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hc123zy, htr138c, htr1810a, htr238a, htr3810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hc135yx, hc478yz, htr138a, htr156a, htr3810a, htr4810a, htr567a, htr678a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc135yx, hc789zy, htr134a, htr156a, htr348a, htr489a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr239a, htr239b, htr239c, _, _⟩
          linarith only [hlam, hc367yz, htr237a, htr239a, htr379c, htr679a])
        obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hd13b, hd910a, htr134a, htr234a, htr239a, htr3910a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc135yx, hc8910yz, htr134a, htr156a, htr348a, htr4810a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc367yz, htr379a, htr679c, htr6910a, htr7910a]
        ·
          linarith only [hlam, hc367yz, htr379b, htr3910a, htr679a, htr7910a]
      ·
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc367yz, htr237a, htr238a, htr378c, htr678a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13b, hd89a, htr134a, htr234a, htr238a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hd13b, hd810a, htr134a, htr234a, htr238a, htr3810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr239a, htr239b, htr239c, _, _⟩
          linarith only [hlam, hc135yx, hc389yz, htr134a, htr156a, htr234a, htr239a, htr568a, htr689a])
        obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc367yz, htr378b, htr3810a, htr678a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc367yz, htr378a, htr678c, htr6810a, htr7810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc135yx, hc8910zy, htr134a, htr156a, htr349a, htr4910a, htr568a, htr6810a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hc135yx, hc489yz, htr139a, htr156a, htr3910a, htr4910a, htr568a, htr689a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd35a, hd910b, htr356a, htr568a, htr689a, htr8910a]
        ·
          linarith only [hlam, hd35a, hd89b, htr235a, htr239a, htr3910a, htr8910a]
    ·
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc356yz, htr367b, htr379a, htr567a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc356yz, htr367a, htr567c, htr579a, htr679a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd36a, hd89b, htr367a, htr567a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hd36a, hd810b, htr367a, htr567a, htr568a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        rcases m.htr 5 6 9 (by decide) (by decide) with
          ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
        ·
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd36a, hd910b, htr367a, htr567a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 5 6 10 (by decide) (by decide) with
            ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
          ·
            rcases m.htr 4 8 9 (by decide) (by decide) with
              ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
            ·
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hc468yz, htr489a, htr689c, htr6910a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc468yz, htr489b, htr4910a, htr689a, htr8910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                linarith only [hlam, hc135yx, hc6910zy, htr015a, htr016a, htr134a, htr156c, htr349a, htr4910a, htr5610a])
              obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
              rcases m.htr 1 6 7 (by decide) (by decide) with
                ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
              ·
                linarith only [hlam, hc136yx, hc6910zy, htr134a, htr167a, htr349a, htr4910a, htr5610a, htr567a]
              ·
                linarith only [hlam, hd12b, hd36a, htr012a, htr016a, htr167a, htr367a]
            ·
              have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr016a, htr016b, htr016c, _, _⟩
                linarith only [hlam, hc135yx, hc689zy, htr015a, htr016a, htr134a, htr156c, htr348a, htr489a, htr569a])
              obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
              rcases m.htr 1 6 7 (by decide) (by decide) with
                ⟨htr167a, htr167b, htr167c, _, _⟩ | ⟨htr167a, htr167b, htr167c, _, _⟩
              ·
                linarith only [hlam, hc136yx, hc689zy, htr134a, htr167a, htr348a, htr489a, htr567a, htr569a]
              ·
                linarith only [hlam, hd12b, hd36a, htr012a, htr016a, htr167a, htr367a]
          ·
            have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
              linarith only [hlam, hc368yz, htr3810a, htr5610a, htr568a, htr6810b])
            obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
            have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr238a, htr238b, htr238c, _, _⟩
              linarith only [hlam, hd13b, hd810a, htr134a, htr234a, htr238a, htr3810a])
            obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
              linarith only [hlam, hd35a, hd68b, htr235a, htr238a, htr389a, htr689a])
            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
            have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
              linarith only [hlam, hc468yz, htr4810a, htr5610a, htr568a, htr6810b])
            obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hd13b, hd810a, htr138a, htr389a, htr4810a, htr489a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hc689zy, htr5610a, htr569a, htr6910b, htr8910a]
            ·
              linarith only [hlam, hd13b, hd910a, htr134a, htr348a, htr489a, htr8910a]
        ·
          have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr239a, htr239b, htr239c, _, _⟩
            linarith only [hlam, hc356yz, htr236a, htr239a, htr369c, htr569a])
          obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc368yz, htr389a, htr568a, htr569a, htr689b])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr238a, htr238b, htr238c, _, _⟩
            linarith only [hlam, hd13b, hd89a, htr134a, htr234a, htr238a, htr389a])
          obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, hd35a, hd68b, htr235a, htr238a, htr3810a, htr6810a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hd13b, hd910a, htr134a, htr234a, htr239a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc468yz, htr489a, htr568a, htr569a, htr689b])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hd13b, hd89a, htr138a, htr3810a, htr4810a, htr489a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc356yz, htr369b, htr3910a, htr569a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hc356yz, htr369a, htr569c, htr5910a, htr6910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            linarith only [hlam, hc135yx, hc8910yz, htr134a, htr157a, htr348a, htr4810a, htr579a, htr7910a]
          ·
            linarith only [hlam, hc135yx, hc379yz, htr134a, htr159a, htr234a, htr239a, htr5910a, htr7910a]
      ·
        have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr238a, htr238b, htr238c, _, _⟩
          linarith only [hlam, hc356yz, htr236a, htr238a, htr368c, htr568a])
        obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd13b, hd89a, htr134a, htr234a, htr238a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hd13b, hd810a, htr134a, htr234a, htr238a, htr3810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc356yz, htr368b, htr389a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc356yz, htr368a, htr568c, htr589a, htr689a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc356yz, htr368b, htr3810a, htr568a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc356yz, htr368a, htr568c, htr5810a, htr6810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc135yx, hc378yz, htr134a, htr158a, htr234a, htr238a, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr239a, htr239b, htr239c, _, _⟩
          linarith only [hlam, hc135yx, hc389yz, htr134a, htr157a, htr234a, htr239a, htr578a, htr789a])
        obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hc356yz, htr236a, htr239a, htr369c, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd36a, hd910b, htr367a, htr567a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hd35a, hd69b, htr235a, htr239a, htr3910a, htr6910a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc135yx, hc489yz, htr139a, htr157a, htr3910a, htr4910a, htr578a, htr789a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc135yx, hc8910zy, htr134a, htr157a, htr349a, htr4910a, htr578a, htr7810a]
        ·
          linarith only [hlam, hc135yx, hc378yz, htr134a, htr158a, htr234a, htr238a, htr5810a, htr7810a]

theorem shard_239 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr037b : m.d 3 7 < m.d 0 7)
    (htr038b : m.d 3 8 < m.d 0 8)
    (htr039b : m.d 3 9 < m.d 0 9)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr138b : m.d 3 8 < m.d 1 8)
    (htr138c : m.d 1 8 < m.d 1 3)
    (htr139a : m.d 3 9 + lam ≤ m.d 1 3)
    (htr139b : m.d 3 9 < m.d 1 9)
    (htr156a : m.d 1 5 + lam ≤ m.d 5 6)
    (htr156c : m.d 1 6 < m.d 5 6)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr158a : m.d 1 5 + lam ≤ m.d 5 8)
    (htr159a : m.d 1 5 + lam ≤ m.d 5 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr349a : m.d 4 9 + lam ≤ m.d 3 4)
    (htr356a : m.d 3 5 + lam ≤ m.d 5 6)
    : False :=
  proof_shard_239 m htr012a htr013a htr015a htr037b htr038b htr039b htr127a htr128a htr129a htr134a htr137a htr137b htr137c htr138a htr138b htr138c htr139a htr139b htr156a htr156c htr157a htr158a htr159a htr234a htr235a htr236a htr236c htr347a htr348a htr349a htr356a

#print axioms shard_239
end Jsp404.NoSatElevenDBMTerminal
