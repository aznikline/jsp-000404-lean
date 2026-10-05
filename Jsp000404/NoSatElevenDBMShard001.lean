import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_001 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr248c : m.d 2 8 < m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr349b : m.d 4 9 < m.d 3 9)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr357a : m.d 5 7 + lam ≤ m.d 3 5)
    (htr357b : m.d 5 7 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr358a : m.d 5 8 + lam ≤ m.d 3 5)
    (htr359b : m.d 5 9 < m.d 3 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd06a := (m.hrange 0 6 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd37a, hd37braw⟩ := m.hrange 3 7 (by decide)
  have hd37b : m.d 3 7 < 4*lam := by
    linarith only [hd37braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd49a := (m.hrange 4 9 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
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
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc017xy, hc017yx, hc017yz, hc017zy⟩ := endpoint_caps m 0 1 7 (by decide) (by decide)
  obtain ⟨hc018xy, hc018yx, hc018yz, hc018zy⟩ := endpoint_caps m 0 1 8 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc349xy, hc349yx, hc349yz, hc349zy⟩ := endpoint_caps m 3 4 9 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc389xy, hc389yx, hc389yz, hc389zy⟩ := endpoint_caps m 3 8 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, hc034yz, htr046a, htr234a, htr236a, htr346b])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hd01a, hd34b, htr013a, htr136a, htr234a, htr236a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc345zy, htr235a, htr236a, htr356b, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 2 3 7 (by decide) (by decide) with
    ⟨htr237a, htr237b, htr237c, _, _⟩ | ⟨htr237a, htr237b, htr237c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr013c, htr037a, htr123c, htr237a])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, htr123c, htr137a, htr237a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, htr136c, htr137b, htr167c])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, htr136b, htr167a, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc678yx, htr123c, htr136a, htr237a, htr367c, htr368a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc346yx, htr234a, htr236c, htr268a, htr368a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr369a, htr369b, htr369c, _, _⟩
      linarith only [hlam, hc679yx, htr123c, htr136a, htr237a, htr367c, htr369a])
    obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hc346yx, htr234a, htr236c, htr269a, htr369a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
      linarith only [hlam, hc6710yx, htr123c, htr136a, htr237a, htr3610a, htr367c])
    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
    have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
      linarith only [hlam, hc346yx, htr234a, htr236c, htr2610a, htr3610a])
    obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
      linarith only [hlam, hd01a, hd78b, htr012a, htr123a, htr237a, htr378a])
    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
      linarith only [hlam, hd01a, hd79b, htr012a, htr123a, htr237a, htr379a])
    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
      linarith only [hlam, hd01a, hd710b, htr012a, htr123a, htr237a, htr3710a])
    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, htr367c, htr378a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, htr367c, htr379a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd01a, hd89b, htr012a, htr126a, htr268a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hd01a, hd68b, htr012a, htr128a, htr289a, htr689a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
      linarith only [hlam, hd01a, hd810b, htr012a, htr126a, htr268a, htr6810a])
    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
      linarith only [hlam, hd01a, hd68b, htr012a, htr128a, htr2810a, htr6810a])
    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
      linarith only [hlam, hd01a, hd910b, htr012a, htr126a, htr269a, htr6910a])
    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
    have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
      linarith only [hlam, hd01a, hd69b, htr012a, htr129a, htr2910a, htr6910a])
    obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
    rcases m.htr 2 3 8 (by decide) (by decide) with
      ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
    ·
      have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr038a, htr038b, htr038c, _, _⟩
        linarith only [hlam, htr013c, htr038a, htr123c, htr238a])
      obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
      have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
        linarith only [hlam, htr238c, htr2810a, htr3810a])
      obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
      rcases m.htr 0 3 6 (by decide) (by decide) with
        ⟨htr036a, htr036b, htr036c, _, _⟩ | ⟨htr036a, htr036b, htr036c, _, _⟩
      ·
        rcases m.htr 2 3 9 (by decide) (by decide) with
          ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
        ·
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, htr239c, htr2910a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 2 3 10 (by decide) (by decide) with
            ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
          ·
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc678zy, htr478a, htr479a, htr689a, htr789c])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc678zy, htr578a, htr579a, htr689a, htr789c])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc014xy, hc6910zy, htr012a, htr047a, htr126a, htr2610a, htr479a, htr7910a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr045a, htr047a, htr347a, htr456a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                linarith only [hlam, hc034yz, htr045a, htr345c, htr357a, htr457a]
              ·
                linarith only [hlam, hd34b, hd910a, htr345a, htr457a, htr579a, htr7910a]
            ·
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc568yz, htr589a, htr689c, htr6910a, htr8910a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 5 7 8 (by decide) (by decide) with
                  ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                ·
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hc035yz, htr057a, htr357c, htr378a, htr578a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hc357zy, htr057a, htr058a, htr378a, htr578c])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                    linarith only [hlam, hc345zy, htr357c, htr378a, htr457a, htr578a])
                  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                    linarith only [hlam, hc357zy, htr378a, htr457a, htr458a, htr578c])
                  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
                  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                    linarith only [hlam, hc014xy, hc689zy, htr012a, htr045a, htr126a, htr269a, htr458a, htr589a])
                  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
                  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                    linarith only [hlam, hc015xy, hc689zy, htr012a, htr058a, htr126a, htr269a, htr589c, htr5910a, htr8910a])
                  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                  rcases m.htr 7 9 10 (by decide) (by decide) with
                    ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  ·
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                      linarith only [hlam, hd34b, hd79a, htr045a, htr047a, htr345a, htr479a])
                    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc034yz, htr047a, htr347c, htr378a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    rcases m.htr 5 7 9 (by decide) (by decide) with
                      ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                    ·
                      linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
                    ·
                      linarith only [hlam, hd34b, hd79a, htr347a, htr478a, htr578a, htr579a]
                  ·
                    rcases m.htr 5 7 9 (by decide) (by decide) with
                      ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                    ·
                      linarith only [hlam, hc357zy, htr379a, htr579b, htr5910a, htr7910a]
                    ·
                      linarith only [hlam, hd37b, hd89a, htr378a, htr578a, htr579a, htr7910a, htr8910a]
                ·
                  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                    linarith only [hlam, hd34b, hd89a, htr345a, htr457a, htr578a, htr789a])
                  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                    linarith only [hlam, hc034yz, htr045a, htr345c, htr357a, htr457a])
                  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
                  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                    linarith only [hlam, hd34b, hd56a, htr045a, htr047a, htr347a, htr456a])
                  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
                  rcases m.htr 4 7 8 (by decide) (by decide) with
                    ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                  ·
                    linarith only [hlam, hc345zy, htr357a, htr457b, htr478a, htr578a]
                  ·
                    linarith only [hlam, hc014xy, hc689zy, htr012a, htr047a, htr126a, htr269a, htr478a, htr789a]
              ·
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd34b, hd910a, htr347a, htr478a, htr789a, htr8910a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                  linarith only [hlam, hc034yz, htr047a, htr347c, htr378a, htr478a])
                obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
                have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                  linarith only [hlam, hc347zy, htr047a, htr048a, htr378a, htr478c])
                obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
                rcases m.htr 4 8 9 (by decide) (by decide) with
                  ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
                ·
                  linarith only [hlam, hc347zy, htr378a, htr478b, htr489a, htr789a]
                ·
                  linarith only [hlam, hc014xy, hc6910zy, htr012a, htr048a, htr126a, htr2610a, htr489a, htr8910a]
          ·
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hc347zy, htr2310a, htr237a, htr3710b, htr4710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
              linarith only [hlam, hc348zy, htr2310a, htr238a, htr3810b, htr4810a])
            obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc378zy, htr2310a, htr238a, htr3810b, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              linarith only [hlam, hc389zy, htr2310a, htr239a, htr3910b, htr8910a])
            obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc014xy, hc6810zy, htr012a, htr047a, htr126a, htr2610a, htr478a, htr7810a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, hd34b, hd810a, htr047a, htr048a, htr347a, htr4810a])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              rcases m.htr 4 8 9 (by decide) (by decide) with
                ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
              ·
                linarith only [hlam, hd46a, hd68b, htr046a, htr048a, htr489a, htr689a]
              ·
                linarith only [hlam, hd34b, hd810a, htr348a, htr489a, htr7810a, htr789a]
            ·
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hd34b, hd910a, htr347a, htr478a, htr789a, htr8910a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr047a, htr047b, htr047c, _, _⟩
                linarith only [hlam, hc034yz, htr047a, htr347c, htr378a, htr478a])
              obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
              have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr048a, htr048b, htr048c, _, _⟩
                linarith only [hlam, hd34b, hd710a, htr047a, htr048a, htr348a, htr4710a])
              obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
              rcases m.htr 4 8 9 (by decide) (by decide) with
                ⟨htr489a, htr489b, htr489c, _, _⟩ | ⟨htr489a, htr489b, htr489c, _, _⟩
              ·
                linarith only [hlam, hd37b, hd810a, htr378a, htr4810a, htr489a, htr789a]
              ·
                linarith only [hlam, hc014xy, hc6910zy, htr012a, htr048a, htr126a, htr2610a, htr489a, htr8910a]
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc034yz, htr049a, htr234a, htr239a, htr349b])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hc349yx, htr234a, htr239c, htr2910a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, hc345zy, htr235a, htr239a, htr359b, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hd34b, hd49a, htr234a, htr239a, htr3910a, htr4910a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr045a, htr045b, htr045c, _, _⟩
            linarith only [hlam, hd34b, hd910a, htr045a, htr049a, htr345a, htr4910a])
          obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
          rcases m.htr 5 9 10 (by decide) (by decide) with
            ⟨htr5910a, htr5910b, htr5910c, _, _⟩ | ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          ·
            linarith only [hlam, hd34b, hd59a, htr234a, htr239a, htr3910a, htr5910a]
          ·
            linarith only [hlam, hc014xy, hc6910zy, htr012a, htr045a, htr126a, htr2610a, htr459a, htr5910a]
      ·
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc346yx, htr034b, htr036a, htr045a, htr345a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc346yx, htr034b, htr036a, htr048a, htr348a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc356yx, htr035b, htr036a, htr057a, htr357a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc356yx, htr035b, htr036a, htr058a, htr358a])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc367xy, htr036a, htr037b, htr078a, htr378a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, hc346yx, htr036a, htr038b, htr089a, htr234c, htr248c, htr289a])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
          linarith only [hlam, hc346yx, htr036a, htr038b, htr0810a, htr234c, htr248c, htr2810a])
        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc014xy, hc678zy, htr012a, htr048a, htr126a, htr268a, htr489a, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc018xy, hc6810zy, htr012a, htr089a, htr126a, htr2610a, htr4810a, htr489a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hc014xy, hc678zy, htr012a, htr045a, htr126a, htr268a, htr457a, htr578a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr458a, htr458b, htr458c, _, _⟩
            linarith only [hlam, hc015xy, hc568yz, htr012a, htr057a, htr126a, htr268a, htr457a, htr458a])
          obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
          rcases m.htr 5 8 10 (by decide) (by decide) with
            ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          ·
            linarith only [hlam, hd56a, hd68b, htr456a, htr458a, htr5810a, htr6810a]
          ·
            linarith only [hlam, hc015xy, hc468yz, htr012a, htr058a, htr126a, htr268a, htr4810a, htr5810a]
        ·
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc017xy, hc468yz, htr012a, htr078a, htr126a, htr268a, htr489a, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc018xy, hc689zy, htr012a, htr0810a, htr126a, htr269a, htr4810a, htr489a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc015xy, hc689zy, htr012a, htr057a, htr126a, htr269a, htr578a, htr789a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr457a, htr457b, htr457c, _, _⟩
            linarith only [hlam, hc345zy, htr357c, htr378a, htr457a, htr578a])
          obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
          have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr458a, htr458b, htr458c, _, _⟩
            linarith only [hlam, hc015xy, hc357zy, htr012a, htr058a, htr123a, htr237a, htr457a, htr458a])
          obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
          rcases m.htr 5 8 10 (by decide) (by decide) with
            ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          ·
            linarith only [hlam, hc014xy, hc568yz, htr012a, htr048a, htr126a, htr268a, htr4810a, htr5810a]
          ·
            linarith only [hlam, hc014xy, hc6810zy, htr012a, htr045a, htr126a, htr2610a, htr458a, htr5810a]
    ·
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, hc346yx, htr136a, htr138a, htr234a, htr238a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd01a, hd34b, htr018a, htr189a, htr234a, htr238c, htr289a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr139a, htr139b, htr139c, _, _⟩
        linarith only [hlam, htr138c, htr139b, htr189c])
      obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc348yx, htr234a, htr238c, htr289a, htr389a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
        linarith only [hlam, hc349yx, htr234a, htr238c, htr289c, htr2910a, htr3910a])
      obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hd34b, hd89a, htr123c, htr139a, htr234a, htr3910a, htr8910a]
      ·
        linarith only [hlam, hd34b, hd910a, htr234a, htr238a, htr389a, htr8910a]
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc034yz, htr047a, htr234a, htr237a, htr347b])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr137a, htr137b, htr137c, _, _⟩
      linarith only [hlam, hc346yx, htr136a, htr137a, htr234a, htr237a])
    obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc345zy, htr235a, htr237a, htr357b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    rcases m.htr 2 3 8 (by decide) (by decide) with
      ⟨htr238a, htr238b, htr238c, _, _⟩ | ⟨htr238a, htr238b, htr238c, _, _⟩
    ·
      have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr138a, htr138b, htr138c, _, _⟩
        linarith only [hlam, htr123c, htr138a, htr238a])
      obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, htr136c, htr138b, htr168c])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, htr137c, htr138b, htr178c])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd01a, hd34b, htr017a, htr178a, htr234a, htr237c, htr278a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, htr136b, htr168a, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc678xy, htr123c, htr136a, htr238a, htr367a, htr368c])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc346yx, htr234a, htr236c, htr267a, htr367a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a]
      ·
        linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr278a, htr678a]
    ·
      rcases m.htr 0 3 6 (by decide) (by decide) with
        ⟨htr036a, htr036b, htr036c, _, _⟩ | ⟨htr036a, htr036b, htr036c, _, _⟩
      ·
        rcases m.htr 2 3 9 (by decide) (by decide) with
          ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
        ·
          have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr139a, htr139b, htr139c, _, _⟩
            linarith only [hlam, htr123c, htr139a, htr239a])
          obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, htr136c, htr139b, htr169c])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, htr137c, htr139b, htr179c])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hd01a, hd34b, htr017a, htr179a, htr234a, htr237c, htr279a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, htr136b, htr169a, htr369a])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc679xy, htr123c, htr136a, htr239a, htr367a, htr369c])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc346yx, htr234a, htr236c, htr267a, htr367a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd01a, hd79b, htr012a, htr126a, htr267a, htr679a]
          ·
            linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr279a, htr679a]
        ·
          rcases m.htr 2 3 10 (by decide) (by decide) with
            ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
          ·
            have hforced1310 := (m.htr 1 3 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1310a, htr1310b, htr1310c, _, _⟩
              linarith only [hlam, htr123c, htr1310a, htr2310a])
            obtain ⟨htr1310a, htr1310b, htr1310c, _, _⟩ := hforced1310
            have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
              linarith only [hlam, htr1310b, htr136c, htr1610c])
            obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
            have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
              linarith only [hlam, htr1310b, htr137c, htr1710c])
            obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, hd01a, hd34b, htr017a, htr1710a, htr234a, htr237c, htr2710a])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              linarith only [hlam, htr136b, htr1610a, htr3610a])
            obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc6710xy, htr123c, htr136a, htr2310a, htr3610c, htr367a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc346yx, htr234a, htr236c, htr267a, htr367a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd01a, hd710b, htr012a, htr126a, htr267a, htr6710a]
            ·
              linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr2710a, htr6710a]
          ·
            rcases m.htr 3 6 7 (by decide) (by decide) with
              ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
            ·
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hc346yx, htr234a, htr236c, htr267a, htr367a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, htr356b, htr367a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr278a, htr678a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc347yx, htr234a, htr237c, htr278a, htr378a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hd34b, hd47a, htr234a, htr237a, htr378a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hd34b, hd78a, htr045a, htr047a, htr345a, htr478a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc014xy, hc678yx, htr012a, htr045a, htr126a, htr267a, htr457a, htr567b, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr234a, htr236a, htr368a, htr568a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc346yx, htr234a, htr236c, htr268a, htr368a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr378a, htr578a]
              ·
                linarith only [hlam, hc014xy, hc678zy, htr012a, htr045a, htr126a, htr268a, htr457a, htr578a]
            ·
              have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                linarith only [hlam, hd06a, hd34b, htr067a, htr234a, htr236a, htr367a])
              obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd34b, hd46a, htr234a, htr236a, htr367a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr045a, htr045b, htr045c, _, _⟩
                linarith only [hlam, hd34b, hd67a, htr045a, htr046a, htr345a, htr467a])
              obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr234a, htr236a, htr367a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc014xy, hc678xy, htr012a, htr045a, htr126a, htr268a, htr456a, htr567a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd34b, hd67a, htr067a, htr068a, htr234a, htr236c, htr268a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd34b, hd67a, htr036c, htr068a, htr234a, htr236a, htr567a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc014xy, hc678yz, htr012a, htr045a, htr127a, htr278a, htr456a, htr568a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc347yx, htr234a, htr237c, htr278a, htr378a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr378a, htr678a]
              ·
                linarith only [hlam, hd34b, hd78a, htr234a, htr236a, htr367a, htr678a]
      ·
        have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr037a, htr037b, htr037c, _, _⟩
          linarith only [hlam, hc346yx, htr036a, htr037a, htr234a, htr237a])
        obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
        have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr045a, htr045b, htr045c, _, _⟩
          linarith only [hlam, hc346yx, htr034b, htr036a, htr045a, htr345a])
        obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
        rcases m.htr 2 3 9 (by decide) (by decide) with
          ⟨htr239a, htr239b, htr239c, _, _⟩ | ⟨htr239a, htr239b, htr239c, _, _⟩
        ·
          have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr039a, htr039b, htr039c, _, _⟩
            linarith only [hlam, htr013c, htr039a, htr123c, htr239a])
          obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr036c, htr039b, htr069c])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr037c, htr039b, htr079c])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr279a, htr279b, htr279c, _, _⟩
            linarith only [hlam, hc347yx, htr037b, htr079a, htr234a, htr237c, htr279a])
          obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, htr036b, htr069a, htr369a])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc679xy, htr123c, htr136a, htr239a, htr367a, htr369c])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr267a, htr267b, htr267c, _, _⟩
            linarith only [hlam, hc346yx, htr234a, htr236c, htr267a, htr367a])
          obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd01a, hd79b, htr012a, htr126a, htr267a, htr679a]
          ·
            linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr279a, htr679a]
        ·
          rcases m.htr 2 3 10 (by decide) (by decide) with
            ⟨htr2310a, htr2310b, htr2310c, _, _⟩ | ⟨htr2310a, htr2310b, htr2310c, _, _⟩
          ·
            have hforced0310 := (m.htr 0 3 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0310a, htr0310b, htr0310c, _, _⟩
              linarith only [hlam, htr013c, htr0310a, htr123c, htr2310a])
            obtain ⟨htr0310a, htr0310b, htr0310c, _, _⟩ := hforced0310
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0310b, htr036c, htr0610c])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0310b, htr037c, htr0710c])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, hc347yx, htr037b, htr0710a, htr234a, htr237c, htr2710a])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              linarith only [hlam, htr036b, htr0610a, htr3610a])
            obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc6710xy, htr123c, htr136a, htr2310a, htr3610c, htr367a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr267a, htr267b, htr267c, _, _⟩
              linarith only [hlam, hc346yx, htr234a, htr236c, htr267a, htr367a])
            obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd01a, hd710b, htr012a, htr126a, htr267a, htr6710a]
            ·
              linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr2710a, htr6710a]
          ·
            rcases m.htr 2 6 7 (by decide) (by decide) with
              ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
            ·
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hc014xy, hc678yx, htr012a, htr045a, htr126a, htr267a, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr234a, htr236a, htr368a, htr568a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc346yx, htr234a, htr236c, htr268a, htr368a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc014xy, hc678zy, htr012a, htr045a, htr126a, htr268a, htr457a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hd34b, hd57a, htr234a, htr237a, htr378a, htr578a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc347yx, htr234a, htr237c, htr278a, htr378a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a]
              ·
                linarith only [hlam, hd01a, hd67b, htr012a, htr127a, htr278a, htr678a]
            ·
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc346yx, htr234a, htr236c, htr267a, htr367a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd34b, hd56a, htr234a, htr236a, htr367a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc014xy, hc678xy, htr012a, htr045a, htr126a, htr268a, htr456a, htr567a])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                linarith only [hlam, hc346yx, htr234a, htr236c, htr268a, htr368a])
              obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd34b, hd67a, htr234a, htr236a, htr368a, htr567a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hc014xy, hc678yz, htr012a, htr045a, htr127a, htr278a, htr456a, htr568a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc347yx, htr234a, htr237c, htr278a, htr378a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              rcases m.htr 6 7 8 (by decide) (by decide) with
                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
              ·
                linarith only [hlam, hd34b, hd67a, htr234a, htr237a, htr378a, htr678a]
              ·
                linarith only [hlam, hd34b, hd78a, htr234a, htr236a, htr367a, htr678a]

theorem shard_001 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013a : m.d 0 1 + lam ≤ m.d 1 3)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr129a : m.d 1 2 + lam ≤ m.d 2 9)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr248c : m.d 2 8 < m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr349b : m.d 4 9 < m.d 3 9)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr357a : m.d 5 7 + lam ≤ m.d 3 5)
    (htr357b : m.d 5 7 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr358a : m.d 5 8 + lam ≤ m.d 3 5)
    (htr359b : m.d 5 9 < m.d 3 9)
    : False :=
  proof_shard_001 m htr012a htr013a htr013c htr017a htr018a htr034b htr035b htr123a htr123c htr126a htr127a htr128a htr129a htr234a htr234c htr235a htr236a htr236c htr248c htr345a htr345c htr346b htr347a htr347b htr347c htr348a htr349b htr356b htr357a htr357b htr357c htr358a htr359b

#print axioms shard_001
end Jsp404.NoSatElevenDBMTerminal
