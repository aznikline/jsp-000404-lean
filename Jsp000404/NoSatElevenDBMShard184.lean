import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_184 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
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
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc018xy, hc018yx, hc018yz, hc018zy⟩ := endpoint_caps m 0 1 8 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, htr013c, htr035a, htr135a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced236 := (m.htr 2 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr236a, htr236b, htr236c, _, _⟩
    linarith only [hlam, hc356yx, htr013c, htr034a, htr135a, htr234a, htr236a])
  obtain ⟨htr236a, htr236b, htr236c, _, _⟩ := hforced236
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hc357yx, htr013c, htr034a, htr135a, htr234a, htr237a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, hc358yx, htr013c, htr034a, htr135a, htr234a, htr238a])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hc456yx, htr013c, htr034a, htr135a, htr345c, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hc123zy, htr014c, htr046a, htr134c, htr234a, htr346a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, hc123zy, htr134c, htr146a, htr234a, htr346a])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc457yx, htr013c, htr034a, htr135a, htr345c, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc123zy, htr014c, htr047a, htr134c, htr234a, htr347a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, hc123zy, htr134c, htr147a, htr234a, htr347a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc458yx, htr013c, htr034a, htr135a, htr345c, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, hc123zy, htr134c, htr148a, htr234a, htr348a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr134a, htr135a, htr234a, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc345xy, htr034a, htr035b, htr056a, htr356a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hd23a, hd57b, htr134a, htr135a, htr234a, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hc345xy, htr034a, htr035b, htr057a, htr357a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hd23a, hd58b, htr134a, htr135a, htr234a, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, hc345xy, htr034a, htr035b, htr058a, htr358a])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  rcases m.htr 1 3 6 (by decide) (by decide) with
    ⟨htr136a, htr136b, htr136c, _, _⟩ | ⟨htr136a, htr136b, htr136c, _, _⟩
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, htr013c, htr036a, htr136a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hd23a, hd67b, htr134a, htr136a, htr234a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc346xy, htr034a, htr036b, htr067a, htr367a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hd23a, hd68b, htr134a, htr136a, htr234a, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc346xy, htr034a, htr036b, htr068a, htr368a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hd23a, hd69b, htr134a, htr136a, htr234a, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
      linarith only [hlam, hd23a, hd610b, htr134a, htr136a, htr234a, htr3610a])
    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
    rcases m.htr 1 3 7 (by decide) (by decide) with
      ⟨htr137a, htr137b, htr137c, _, _⟩ | ⟨htr137a, htr137b, htr137c, _, _⟩
    ·
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd23a, hd78b, htr134a, htr137a, htr234a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hd23a, hd79b, htr134a, htr137a, htr234a, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
        linarith only [hlam, hd23a, hd710b, htr134a, htr137a, htr234a, htr3710a])
      obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
      rcases m.htr 1 3 8 (by decide) (by decide) with
        ⟨htr138a, htr138b, htr138c, _, _⟩ | ⟨htr138a, htr138b, htr138c, _, _⟩
      ·
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr134a, htr138a, htr234a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hd23a, hd810b, htr134a, htr138a, htr234a, htr3810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        rcases m.htr 1 3 9 (by decide) (by decide) with
          ⟨htr139a, htr139b, htr139c, _, _⟩ | ⟨htr139a, htr139b, htr139c, _, _⟩
        ·
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr134a, htr139a, htr234a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 1 3 10 (by decide) (by decide) with
            ⟨htr1310a, htr1310b, htr1310c, _, _⟩ | ⟨htr1310a, htr1310b, htr1310c, _, _⟩
          ·
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hc235yz, htr256a, htr356c, htr367a, htr567a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                linarith only [hlam, hc356zy, htr256a, htr257a, htr367a, htr567c])
              obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hc356zy, htr367c, htr378a, htr567a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc356zy, htr367a, htr567b, htr578a, htr678a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc356zy, htr367c, htr379a, htr567a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc356zy, htr367a, htr567b, htr579a, htr679a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr578a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd12b, hd910a, htr125a, htr257a, htr579a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc378zy, htr389c, htr3910a, htr789a, htr8910a]
              ·
                linarith only [hlam, hc378zy, htr389a, htr789b, htr7910a, htr8910a]
            ·
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, hc236yz, htr267a, htr367c, htr378a, htr678a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hc367zy, htr267a, htr268a, htr378a, htr678c])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc367zy, htr378a, htr567a, htr568a, htr678c])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc367zy, htr378c, htr389a, htr678a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                  linarith only [hlam, hc367zy, htr268b, htr289a, htr378a, htr678b, htr789a])
                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                  linarith only [hlam, htr268c, htr269b, htr289c])
                obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                  linarith only [hlam, hd12b, hd89a, htr125a, htr256a, htr568a, htr689a])
                obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
                have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  linarith only [hlam, hd12b, hd910a, htr126a, htr268a, htr689a, htr8910a])
                obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd12b, hd89a, htr126a, htr269a, htr6910a, htr8910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                rcases m.htr 6 7 9 (by decide) (by decide) with
                  ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                ·
                  rcases m.htr 7 9 10 (by decide) (by decide) with
                    ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  ·
                    linarith only [hlam, hc367zy, htr379c, htr3910a, htr679a, htr7910a]
                  ·
                    linarith only [hlam, hc367zy, htr379a, htr679b, htr6910a, htr7910a]
                ·
                  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                    linarith only [hlam, hd35b, hd79a, htr256a, htr257a, htr356a, htr567b, htr679a])
                  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                  rcases m.htr 5 7 8 (by decide) (by decide) with
                    ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                  ·
                    linarith only [hlam, hc235yz, htr257a, htr357c, htr378a, htr578a]
                  ·
                    linarith only [hlam, hd35b, hd79a, htr357a, htr578a, htr678a, htr679a]
              ·
                have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                  linarith only [hlam, hd12b, hd78a, htr125a, htr256a, htr567a, htr678a])
                obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
                have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                  linarith only [hlam, hd35b, hd78a, htr256a, htr257a, htr356a, htr567b, htr678a])
                obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hc235yz, htr257a, htr357c, htr379a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hd35b, hd78a, htr357a, htr579a, htr678a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd35b, hd89a, htr356a, htr567a, htr678a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hd35b, hd910a, htr356a, htr567a, htr679a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hc378zy, htr389c, htr3910a, htr789a, htr8910a]
                ·
                  linarith only [hlam, hc378zy, htr389a, htr789b, htr7910a, htr8910a]
          ·
            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              linarith only [hlam, hc356zy, htr1310a, htr136a, htr3610b, htr5610a])
            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
            have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
              linarith only [hlam, hc357zy, htr1310a, htr137a, htr3710b, htr5710a])
            obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc367zy, htr1310a, htr137a, htr3710b, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc378zy, htr1310a, htr138a, htr3810b, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hc235yz, htr256a, htr356c, htr367a, htr567a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                linarith only [hlam, hd35b, hd610a, htr256a, htr257a, htr357a, htr5610a])
              obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd12b, hd810a, htr125a, htr257a, htr578a, htr7810a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hc356zy, htr367c, htr378a, htr567a, htr678a]
              ·
                linarith only [hlam, hd36b, hd710a, htr367a, htr5710a, htr578a, htr678a]
            ·
              have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr256a, htr256b, htr256c, _, _⟩
                linarith only [hlam, hd12b, hd710a, htr125a, htr256a, htr567a, htr6710a])
              obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
              have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr257a, htr257b, htr257c, _, _⟩
                linarith only [hlam, hd35b, hd710a, htr256a, htr257a, htr356a, htr5710a])
              obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc235yz, htr257a, htr357c, htr378a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd35b, hd710a, htr357a, htr578a, htr6710a, htr678a]
              ·
                linarith only [hlam, hd35b, hd810a, htr356a, htr567a, htr678a, htr7810a]
        ·
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc356zy, htr136a, htr139a, htr369b, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc357zy, htr137a, htr139a, htr379b, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc367zy, htr137a, htr139a, htr379b, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc378zy, htr138a, htr139a, htr389b, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hc235yz, htr256a, htr356c, htr367a, htr567a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hd35b, hd69a, htr256a, htr257a, htr357a, htr569a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr578a, htr789a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hc356zy, htr367c, htr378a, htr567a, htr678a]
            ·
              linarith only [hlam, hd36b, hd79a, htr367a, htr578a, htr579a, htr678a]
          ·
            have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr256a, htr256b, htr256c, _, _⟩
              linarith only [hlam, hd12b, hd79a, htr125a, htr256a, htr567a, htr679a])
            obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
            have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr257a, htr257b, htr257c, _, _⟩
              linarith only [hlam, hd35b, hd79a, htr256a, htr257a, htr356a, htr579a])
            obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc235yz, htr257a, htr357c, htr378a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd35b, hd79a, htr357a, htr578a, htr678a, htr679a]
            ·
              linarith only [hlam, hd35b, hd89a, htr356a, htr567a, htr678a, htr789a]
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc235yz, htr135a, htr138a, htr258a, htr358b])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc356zy, htr136a, htr138a, htr368b, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc357zy, htr137a, htr138a, htr378b, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc367zy, htr137a, htr138a, htr378b, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hc235yz, htr256a, htr356c, htr367a, htr567a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hd35b, hd68a, htr256a, htr257a, htr357a, htr568a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc356zy, htr367c, htr379a, htr567a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd36b, hd78a, htr367a, htr578a, htr579a, htr679a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc012xy, hc789yz, htr014a, htr025a, htr148a, htr257a, htr489a, htr579a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc016xy, hc468zy, htr018a, htr067a, htr189a, htr489a, htr567a, htr568a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc358yx, htr135a, htr138c, htr189a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd35b, hd78a, htr135a, htr138a, htr389a, htr789a]
          ·
            linarith only [hlam, hd36b, hd89a, htr367a, htr567a, htr568a, htr678b, htr789a]
        ·
          have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr256a, htr256b, htr256c, _, _⟩
            linarith only [hlam, hd12b, hd78a, htr125a, htr256a, htr567a, htr678a])
          obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
          have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr257a, htr257b, htr257c, _, _⟩
            linarith only [hlam, hd35b, hd78a, htr256a, htr257a, htr356a, htr578a])
          obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc235yz, htr257a, htr357c, htr379a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd35b, hd89a, htr256a, htr258a, htr356a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd35b, hd58a, htr135a, htr138a, htr389a, htr589a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc358yx, htr135a, htr138c, htr189a, htr389a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc015xy, hc478zy, htr018a, htr056a, htr189a, htr489a, htr567a, htr678a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd35b, hd78a, htr357a, htr579a, htr678a, htr679a]
          ·
            linarith only [hlam, hc015xy, hc789yz, htr014a, htr056a, htr148a, htr489a, htr567a, htr679a]
    ·
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc123zy, htr034a, htr037a, htr137a, htr234a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc235yz, htr135a, htr137a, htr257a, htr357b])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc356zy, htr136a, htr137a, htr367b, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 2 5 6 (by decide) (by decide) with
        ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
      ·
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc235yz, htr256a, htr356c, htr368a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd35b, hd78a, htr256a, htr257a, htr356a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd35b, hd57a, htr135a, htr137a, htr378a, htr578a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc357yx, htr135a, htr137c, htr178a, htr378a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc015xy, hc457zy, htr017a, htr056a, htr178a, htr256a, htr257a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc015xy, hc578yz, htr014a, htr056a, htr147a, htr256a, htr258a, htr478a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc235yz, htr013c, htr038a, htr135a, htr258a, htr358b])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc789yx, htr037a, htr038a, htr378c, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr034a, htr038a, htr234a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr237a, htr379a, htr478a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc235yz, htr258a, htr358c, htr389a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc015xy, hc678yz, htr014a, htr058a, htr147a, htr478a, htr589a, htr689a]
        ·
          linarith only [hlam, hc015xy, hc789zy, htr014a, htr056a, htr147a, htr479a, htr568a, htr689a]
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hd35b, hd67a, htr256a, htr258a, htr358a, htr567a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr125a, htr256a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd35b, hd67a, htr135a, htr137a, htr378a, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc357yx, htr135a, htr137c, htr178a, htr378a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc012xy, hc467zy, htr017a, htr025a, htr178a, htr256a, htr478a, htr567a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc012xy, hc678yz, htr014a, htr025a, htr147a, htr256a, htr478a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc356zy, htr013c, htr038a, htr136a, htr368b, htr568a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc789yx, htr037a, htr038a, htr378c, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr034a, htr038a, htr234a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr237a, htr379a, htr478a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc012xy, hc789zy, htr014a, htr025a, htr147a, htr258a, htr479a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc356zy, htr368c, htr389a, htr568a, htr689a]
        ·
          linarith only [hlam, hc016xy, hc578yz, htr014a, htr068a, htr147a, htr478a, htr589a, htr689a]
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc123zy, htr034a, htr036a, htr136a, htr234a])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hc235yz, htr135a, htr136a, htr256a, htr356b])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    rcases m.htr 1 3 7 (by decide) (by decide) with
      ⟨htr137a, htr137b, htr137c, _, _⟩ | ⟨htr137a, htr137b, htr137c, _, _⟩
    ·
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, htr013c, htr037a, htr137a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr036c, htr037b, htr067c])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, htr036b, htr067a, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc678yx, htr013c, htr036a, htr137a, htr367c, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hc679yx, htr013c, htr036a, htr137a, htr367c, htr369a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
        linarith only [hlam, hc6710yx, htr013c, htr036a, htr137a, htr3610a, htr367c])
      obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd23a, hd78b, htr134a, htr137a, htr234a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc347xy, htr034a, htr037b, htr078a, htr378a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd23a, hd46b, htr134a, htr137a, htr234a, htr367c, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr236a, htr368a, htr467a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr236a, htr369a, htr467a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr236a, htr3610a, htr4610a, htr467a])
      obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, htr367c, htr378a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hd23a, hd810b, htr234a, htr346a, htr468a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc012xy, hc678zy, htr014a, htr025a, htr146a, htr257a, htr468a, htr578a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc015xy, hc568yz, htr014a, htr057a, htr146a, htr257a, htr258a, htr468a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 5 8 9 (by decide) (by decide) with
          ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
        ·
          linarith only [hlam, hd56a, hd68b, htr256a, htr258a, htr589a, htr689a]
        ·
          linarith only [hlam, hc015xy, hc678zy, htr014a, htr058a, htr146a, htr468a, htr589a, htr789a]
      ·
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc012xy, hc689zy, htr014a, htr027a, htr146a, htr278a, htr469a, htr789a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
          linarith only [hlam, hc267yz, htr078b, htr0810a, htr278a, htr678c, htr6810a])
        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc017xy, hc268yz, htr014a, htr078a, htr146a, htr289a, htr468a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc018xy, hc689zy, htr014a, htr0810a, htr146a, htr2810a, htr289a, htr469a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc015xy, hc689zy, htr014a, htr057a, htr146a, htr469a, htr578a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc235yz, htr257a, htr357c, htr378a, htr578a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc015xy, hc567yz, htr014a, htr058a, htr146a, htr257a, htr258a, htr467a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 5 8 10 (by decide) (by decide) with
          ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
        ·
          linarith only [hlam, hc012xy, hc568yz, htr014a, htr028a, htr146a, htr2810a, htr468a, htr5810a]
        ·
          linarith only [hlam, hc012xy, hc6810zy, htr014a, htr025a, htr146a, htr258a, htr4610a, htr5810a]
    ·
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc123zy, htr034a, htr037a, htr137a, htr234a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc235yz, htr135a, htr137a, htr257a, htr357b])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      rcases m.htr 1 3 8 (by decide) (by decide) with
        ⟨htr138a, htr138b, htr138c, _, _⟩ | ⟨htr138a, htr138b, htr138c, _, _⟩
      ·
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, htr013c, htr038a, htr138a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr036c, htr038b, htr068c])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr037c, htr038b, htr078c])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, htr036b, htr068a, htr368a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc678xy, htr013c, htr036a, htr138a, htr367a, htr368c])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, htr037b, htr078a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd23a, hd46b, htr134a, htr138a, htr234a, htr368c, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd23a, hd68b, htr236a, htr367a, htr467a, htr468a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a]
        ·
          linarith only [hlam, hd23a, hd67b, htr134a, htr138a, htr234a, htr378c, htr678a]
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc235yz, htr135a, htr138a, htr258a, htr358b])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 1 3 9 (by decide) (by decide) with
          ⟨htr139a, htr139b, htr139c, _, _⟩ | ⟨htr139a, htr139b, htr139c, _, _⟩
        ·
          have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr039a, htr039b, htr039c, _, _⟩
            linarith only [hlam, htr013c, htr039a, htr139a])
          obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr036c, htr039b, htr069c])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr037c, htr039b, htr079c])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, htr036b, htr069a, htr369a])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc679xy, htr013c, htr036a, htr139a, htr367a, htr369c])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, htr037b, htr079a, htr379a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hd23a, hd46b, htr134a, htr139a, htr234a, htr369c, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd23a, hd69b, htr236a, htr367a, htr467a, htr469a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd79b, htr234a, htr346a, htr467a, htr679a]
          ·
            linarith only [hlam, hd23a, hd67b, htr134a, htr139a, htr234a, htr379c, htr679a]
        ·
          rcases m.htr 1 3 10 (by decide) (by decide) with
            ⟨htr1310a, htr1310b, htr1310c, _, _⟩ | ⟨htr1310a, htr1310b, htr1310c, _, _⟩
          ·
            have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
              linarith only [hlam, htr013c, htr0310a, htr1310a])
            obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0310b, htr036c, htr0610c])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0310b, htr037c, htr0710c])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              linarith only [hlam, htr036b, htr0610a, htr3610a])
            obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc6710xy, htr013c, htr036a, htr1310a, htr3610c, htr367a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
              linarith only [hlam, htr037b, htr0710a, htr3710a])
            obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, hd23a, hd46b, htr1310a, htr134a, htr234a, htr3610c, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd23a, hd610b, htr236a, htr367a, htr4610a, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd710b, htr234a, htr346a, htr467a, htr6710a]
            ·
              linarith only [hlam, hd23a, hd67b, htr1310a, htr134a, htr234a, htr3710c, htr6710a]
          ·
            rcases m.htr 3 6 7 (by decide) (by decide) with
              ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
            ·
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hc356yx, htr016c, htr067a, htr135a, htr136c, htr367a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc356yx, htr135a, htr136c, htr167a, htr367a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, htr236c, htr267a, htr367a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, htr356b, htr367a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              rcases m.htr 4 6 7 (by decide) (by decide) with
                ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
              ·
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc012xy, hc678yx, htr014a, htr025a, htr146a, htr256a, htr467a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                  linarith only [hlam, hd35b, hd56a, htr135a, htr136a, htr368a, htr568a])
                obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hd23a, hd67b, htr236a, htr368a, htr467a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hc012xy, hc679yx, htr014a, htr025a, htr146a, htr256a, htr467a, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                  linarith only [hlam, hd35b, hd56a, htr135a, htr136a, htr369a, htr569a])
                obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                  linarith only [hlam, hd23a, hd67b, htr236a, htr369a, htr467a, htr469a])
                obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc012xy, hc678zy, htr014a, htr025a, htr146a, htr257a, htr468a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hd35b, hd57a, htr135a, htr137a, htr378a, htr578a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc012xy, hc689zy, htr014a, htr025a, htr146a, htr258a, htr469a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd23a, hd68b, htr237a, htr378a, htr689a, htr789a]
                ·
                  linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hd23a, hd68b, htr236a, htr367a, htr467a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                rcases m.htr 5 6 8 (by decide) (by decide) with
                  ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, hc456zy, htr016c, htr068a, htr167a, htr467a, htr568a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, hc456zy, htr167a, htr168a, htr467a, htr568a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  rcases m.htr 5 6 9 (by decide) (by decide) with
                    ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
                  ·
                    rcases m.htr 5 6 10 (by decide) (by decide) with
                      ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                    ·
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hd23a, hd47b, htr236a, htr367a, htr478a, htr678a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hc012xy, hc789yx, htr016a, htr025a, htr167a, htr257a, htr579a, htr678a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, hc456zy, htr067c, htr079a, htr467a, htr567b, htr579a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hd23a, hd78b, htr034b, htr047b, htr079a, htr234a, htr478a, htr479a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hc012xy, hc789zy, htr014a, htr025a, htr147a, htr258a, htr479a, htr589a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc456zy, htr468a, htr568b, htr589a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd23a, hd89b, htr236a, htr367a, htr678a, htr789a]
                        ·
                          linarith only [hlam, hd23a, hd78b, htr034b, htr046b, htr068a, htr234a, htr689a, htr789a]
                      ·
                        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                          linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a])
                        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc456zy, htr467a, htr567b, htr578a, htr678a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                          linarith only [hlam, hc012xy, hc789xy, htr016a, htr025a, htr167a, htr257a, htr578a, htr679a])
                        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc246yz, htr267b, htr279a, htr467a, htr679a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hd35b, hd78a, htr135a, htr137a, htr237c, htr279a, htr578a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc012xy, hc789yz, htr014a, htr025a, htr148a, htr257a, htr489a, htr579a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc012xy, hc478zy, htr018a, htr025a, htr189a, htr257a, htr489a, htr578a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                          linarith only [hlam, hc456zy, htr168c, htr189a, htr258b, htr289a, htr468a, htr568b])
                        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd35b, hd78a, htr135a, htr138a, htr238c, htr289a, htr789a]
                        ·
                          linarith only [hlam, hd35b, hd89a, htr135a, htr137a, htr237c, htr278a, htr789a]
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
                      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                        linarith only [hlam, hc246yz, htr067c, htr0710a, htr267b, htr2710a, htr467a])
                      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                        linarith only [hlam, hc456zy, htr068c, htr0810a, htr258b, htr2810a, htr468a, htr568b])
                      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                        linarith only [hlam, hd35b, hd610a, htr135a, htr137a, htr237c, htr2710a, htr5610a, htr567b, htr5710a])
                      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hc012xy, hc7810yx, htr016a, htr025a, htr167a, htr257a, htr5710a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                        linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a])
                      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                      rcases m.htr 7 8 10 (by decide) (by decide) with
                        ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      ·
                        linarith only [hlam, hd35b, hd78a, htr135a, htr138a, htr238c, htr2810a, htr7810a]
                      ·
                        linarith only [hlam, hd35b, hd810a, htr135a, htr137a, htr237c, htr278a, htr7810a]
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
                    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                      linarith only [hlam, hc246yz, htr067c, htr079a, htr267b, htr279a, htr467a])
                    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hc456zy, htr068c, htr089a, htr258b, htr289a, htr468a, htr568b])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                      linarith only [hlam, hd35b, hd69a, htr135a, htr137a, htr237c, htr279a, htr567b, htr569a, htr579a])
                    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hc012xy, hc789yx, htr016a, htr025a, htr167a, htr257a, htr579a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                      linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a])
                    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hd35b, hd78a, htr135a, htr138a, htr238c, htr289a, htr789a]
                    ·
                      linarith only [hlam, hd35b, hd89a, htr135a, htr137a, htr237c, htr278a, htr789a]
                ·
                  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                    linarith only [hlam, htr056b, htr068a, htr568a])
                  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                    linarith only [hlam, htr067b, htr068c, htr078b])
                  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                    linarith only [hlam, htr016c, htr056b, htr168a, htr568a])
                  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                    linarith only [hlam, hc246yz, htr067c, htr078a, htr267b, htr278a, htr467a])
                  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd35b, hd68a, htr135a, htr137a, htr237c, htr278a, htr567b, htr568a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc012xy, hc789xy, htr016a, htr025a, htr167a, htr257a, htr578a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc246yz, htr267b, htr279a, htr467a, htr679a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd35b, hd68a, htr135a, htr137a, htr237c, htr279a, htr567b, htr568a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc012xy, hc789yz, htr014a, htr025a, htr148a, htr257a, htr489a, htr579a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc012xy, hc468zy, htr018a, htr025a, htr189a, htr256a, htr489a, htr568a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd46b, hd78a, htr167a, htr168c, htr189a, htr467a, htr789a]
                  ·
                    linarith only [hlam, hd35b, hd89a, htr135a, htr137a, htr237c, htr278a, htr789a]
            ·
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, htr036b, htr067a, htr367a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd35b, hd56a, htr135a, htr136a, htr367a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd35b, hd78a, htr135a, htr136a, htr367a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hd35b, hd67a, htr135a, htr137a, htr378a, htr678a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc357yx, htr135a, htr137c, htr178a, htr378a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc012xy, hc467zy, htr017a, htr025a, htr178a, htr256a, htr478a, htr567a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc012xy, hc678yz, htr014a, htr025a, htr147a, htr256a, htr478a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd35b, hd67a, htr016c, htr068a, htr135a, htr136c, htr567a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc012xy, hc789yx, htr014a, htr025a, htr147a, htr257a, htr478a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hc678xy, htr067c, htr068a, htr079a, htr567b, htr579a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hd23a, hd78b, htr034b, htr047b, htr079a, htr234a, htr478a, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc012xy, hc789zy, htr014a, htr025a, htr147a, htr258a, htr479a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc678xy, htr567a, htr568b, htr589a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
              ·
                linarith only [hlam, hd67a, hd78b, htr567a, htr568a, htr689a, htr789a]

theorem shard_184 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 4 5)
    : False :=
  proof_shard_184 m htr013c htr014a htr014c htr016a htr016c htr017a htr018a htr025a htr027a htr028a htr034a htr034b htr125a htr126a htr134a htr134c htr135a htr234a htr345c

#print axioms shard_184
end Jsp404.NoSatElevenDBMTerminal
