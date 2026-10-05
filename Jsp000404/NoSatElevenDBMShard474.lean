import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_474 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348c : m.d 3 8 < m.d 4 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  have hd37a := (m.hrange 3 7 (by decide)).1
  have hd38a := (m.hrange 3 8 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  obtain ⟨hd48a, hd48braw⟩ := m.hrange 4 8 (by decide)
  have hd48b : m.d 4 8 < 4*lam := by
    linarith only [hd48braw, hp]
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
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc379xy, hc379yx, hc379yz, hc379zy⟩ := endpoint_caps m 3 7 9 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, htr013b, htr036a, htr136a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
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
    linarith only [hlam, hc567xy, htr135a, htr136a, htr356b, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc345xy, htr134a, htr135b, htr157a, htr357a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc568xy, htr135a, htr136a, htr356b, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hc345xy, htr134a, htr135b, htr158a, htr358a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hc569xy, htr135a, htr136a, htr356b, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd23b, hd67a, htr135a, htr136a, htr235a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd23b, hd68a, htr135a, htr136a, htr235a, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, hd23b, hd69a, htr135a, htr136a, htr235a, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
    linarith only [hlam, hd23b, hd610a, htr135a, htr136a, htr235a, htr3610a])
  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
  rcases m.htr 0 3 5 (by decide) (by decide) with
    ⟨htr035a, htr035b, htr035c, _, _⟩ | ⟨htr035a, htr035b, htr035c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hc345xy, htr034c, htr035a, htr046a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc345xy, htr034c, htr035a, htr048a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc356yx, htr035a, htr036c, htr067a, htr367a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc356yx, htr035a, htr036c, htr068a, htr368a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    rcases m.htr 1 3 7 (by decide) (by decide) with
      ⟨htr137a, htr137b, htr137c, _, _⟩ | ⟨htr137a, htr137b, htr137c, _, _⟩
    ·
      have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr037a, htr037b, htr037c, _, _⟩
        linarith only [hlam, hc345xy, htr035a, htr037a, htr134a, htr137a])
      obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc234zy, htr134a, htr137a, htr247a, htr347c])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hc346yz, htr136a, htr137a, htr367c, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      rcases m.htr 2 4 6 (by decide) (by decide) with
        ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr246a, htr248a, htr348a, htr467a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12a, hd78b, htr124a, htr246a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr134a, htr137a, htr378a, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc347xy, htr134a, htr137b, htr178a, htr378a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc012yx, hc567yz, htr017a, htr024a, htr178a, htr246a, htr467a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc012yx, hc678zy, htr015a, htr024a, htr157a, htr246a, htr468a, htr578a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc346yz, htr013b, htr038a, htr136a, htr368c, htr468a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc789xy, htr037a, htr038a, htr378b, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd23b, hd89a, htr035a, htr038a, htr235a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr237a, htr379a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc012yx, hc789yz, htr015a, htr024a, htr157a, htr248a, htr489a, htr579a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc016yx, hc478zy, htr015a, htr068a, htr157a, htr489a, htr578a, htr689a]
        ·
          linarith only [hlam, hc346yz, htr368b, htr389a, htr468a, htr689a]
      ·
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd36a, hd45b, htr245a, htr246a, htr368a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd34a, hd78b, htr246a, htr247a, htr346a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34a, hd47b, htr134a, htr137a, htr378a, htr478a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc347xy, htr134a, htr137b, htr178a, htr378a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd34a, hd79b, htr246a, htr247a, htr346a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd34a, hd47b, htr134a, htr137a, htr379a, htr479a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc347xy, htr134a, htr137b, htr179a, htr379a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc014yx, hc457zy, htr017a, htr046a, htr178a, htr246a, htr247a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc014yx, hc478zy, htr015a, htr046a, htr157a, htr246a, htr248a, htr578a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc234zy, htr013b, htr038a, htr134a, htr248a, htr348c])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd23b, hd89a, htr035a, htr038a, htr235a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd38a, hd45b, htr245a, htr248a, htr389a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc014yx, hc457zy, htr017a, htr046a, htr179a, htr246a, htr247a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc014yx, hc789yz, htr015a, htr046a, htr157a, htr468a, htr579a, htr689a]
        ·
          linarith only [hlam, hc014yx, hc678zy, htr015a, htr048a, htr157a, htr489a, htr578a, htr689a]
    ·
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr135a, htr137a, htr235a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hd23b, hd79a, htr135a, htr137a, htr235a, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
        linarith only [hlam, hd23b, hd710a, htr135a, htr137a, htr235a, htr3710a])
      obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
      rcases m.htr 1 3 8 (by decide) (by decide) with
        ⟨htr138a, htr138b, htr138c, _, _⟩ | ⟨htr138a, htr138b, htr138c, _, _⟩
      ·
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc234zy, htr134a, htr138a, htr248a, htr348c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc346yz, htr136a, htr138a, htr368c, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc347yz, htr137a, htr138a, htr378c, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc367yz, htr137a, htr138a, htr378c, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        rcases m.htr 4 6 7 (by decide) (by decide) with
          ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
        ·
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hd12a, hd78b, htr124a, htr246a, htr467a, htr678a])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hd34a, hd78b, htr246a, htr247a, htr346a, htr478a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd37a, hd45b, htr245a, htr247a, htr379a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd34a, hd89b, htr246a, htr248a, htr346a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hd34a, hd48b, htr134a, htr138a, htr389a, htr489a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc348xy, htr134a, htr138b, htr189a, htr389a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc014yx, hc578yz, htr018a, htr046a, htr189a, htr467a, htr589a, htr678a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hc014yx, hc789zy, htr015a, htr046a, htr158a, htr467a, htr589a, htr679a]
          ·
            linarith only [hlam, hd34a, hd78b, htr347a, htr479a, htr678a, htr679a]
        ·
          have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr246a, htr246b, htr246c, _, _⟩
            linarith only [hlam, hd36a, hd45b, htr245a, htr246a, htr367a, htr467a])
          obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
          have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr247a, htr247b, htr247c, _, _⟩
            linarith only [hlam, hd34a, hd68b, htr246a, htr247a, htr347a, htr468a])
          obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc346yz, htr367b, htr379a, htr467a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hd36a, hd78b, htr367a, htr478a, htr479a, htr679a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc012yx, hc789zy, htr015a, htr024a, htr158a, htr247a, htr479a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc016yx, hc568yz, htr018a, htr067a, htr189a, htr467a, htr468a, htr589a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc348xy, htr134a, htr138b, htr189a, htr389a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd36a, hd89b, htr367a, htr467a, htr468a, htr678c, htr789a]
          ·
            linarith only [hlam, hd34a, hd78b, htr134a, htr138a, htr389a, htr789a]
      ·
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd23b, hd89a, htr135a, htr138a, htr235a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hd23b, hd810a, htr135a, htr138a, htr235a, htr3810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        rcases m.htr 1 3 9 (by decide) (by decide) with
          ⟨htr139a, htr139b, htr139c, _, _⟩ | ⟨htr139a, htr139b, htr139c, _, _⟩
        ·
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hc346yz, htr136a, htr139a, htr369c, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc347yz, htr137a, htr139a, htr379c, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hc367yz, htr137a, htr139a, htr379c, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc378yz, htr138a, htr139a, htr389c, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd34a, hd89b, htr346a, htr467a, htr678a, htr789a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr246a, htr246b, htr246c, _, _⟩
              linarith only [hlam, hd36a, hd45b, htr245a, htr246a, htr367a, htr467a])
            obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, hd34a, hd69b, htr246a, htr247a, htr347a, htr469a])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd89b, htr124a, htr247a, htr478a, htr789a]
            ·
              linarith only [hlam, hd36a, hd79b, htr367a, htr478a, htr479a, htr678a]
          ·
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr246a, htr246b, htr246c, _, _⟩
              linarith only [hlam, hd12a, hd79b, htr124a, htr246a, htr467a, htr679a])
            obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
            have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr247a, htr247b, htr247c, _, _⟩
              linarith only [hlam, hd34a, hd79b, htr246a, htr247a, htr346a, htr479a])
            obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              linarith only [hlam, hd34a, hd79b, htr347a, htr478a, htr678a, htr679a]
            ·
              linarith only [hlam, hd37a, hd45b, htr245a, htr247a, htr378a, htr478a]
        ·
          have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
            linarith only [hlam, hd23b, hd910a, htr135a, htr139a, htr235a, htr3910a])
          obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
          rcases m.htr 1 3 10 (by decide) (by decide) with
            ⟨htr1310a, htr1310b, htr1310c, _, _⟩ | ⟨htr1310a, htr1310b, htr1310c, _, _⟩
          ·
            have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
              linarith only [hlam, hc237zy, htr1310a, htr137a, htr2710a, htr3710c])
            obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, hc346yz, htr1310a, htr136a, htr3610c, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hc347yz, htr1310a, htr137a, htr3710c, htr4710a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              linarith only [hlam, hc367yz, htr1310a, htr137a, htr3710c, htr6710a])
            obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc378yz, htr1310a, htr138a, htr3810c, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hc379yz, htr1310a, htr139a, htr3910c, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hd36a, hd710b, htr2710a, htr278a, htr367a, htr678a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hd37a, hd810b, htr278a, htr279a, htr379a, htr7810a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hd34a, hd810b, htr346a, htr467a, htr678a, htr7810a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr246a, htr246b, htr246c, _, _⟩
                linarith only [hlam, hd36a, hd45b, htr245a, htr246a, htr367a, htr467a])
              obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
              have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                linarith only [hlam, hd34a, hd610b, htr246a, htr247a, htr347a, htr4610a])
              obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
              rcases m.htr 4 7 9 (by decide) (by decide) with
                ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd910b, htr124a, htr247a, htr479a, htr7910a]
              ·
                linarith only [hlam, hd12a, hd710b, htr127a, htr279a, htr4710a, htr479a]
            ·
              have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                linarith only [hlam, hd12a, hd710b, htr127a, htr278a, htr6710a, htr678a])
              obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
              have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                linarith only [hlam, hd37a, hd910b, htr278a, htr279a, htr378a, htr7910a])
              obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr246a, htr246b, htr246c, _, _⟩
                linarith only [hlam, hd12a, hd710b, htr124a, htr246a, htr467a, htr6710a])
              obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
              have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                linarith only [hlam, hd34a, hd710b, htr246a, htr247a, htr346a, htr4710a])
              obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
              rcases m.htr 4 7 9 (by decide) (by decide) with
                ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
              ·
                linarith only [hlam, hd34a, hd710b, htr2710a, htr279a, htr347a, htr479a]
              ·
                linarith only [hlam, hd37a, hd45b, htr245a, htr247a, htr379a, htr479a]
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
                have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr246a, htr246b, htr246c, _, _⟩
                  linarith only [hlam, hd36a, hd45b, htr245a, htr246a, htr367a, htr467a])
                obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
                have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                  linarith only [hlam, hc346yz, htr246a, htr247a, htr367a, htr467b])
                obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
                rcases m.htr 4 7 8 (by decide) (by decide) with
                  ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                ·
                  linarith only [hlam, hd12a, hd89b, htr124a, htr247a, htr478a, htr789a]
                ·
                  linarith only [hlam, hc346yz, htr367a, htr467c, htr478a, htr678a]
              ·
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc347yz, htr378b, htr389a, htr478a, htr789a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc378yz, htr389a, htr478a, htr479a, htr789b])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc378yz, htr389a, htr678a, htr679a, htr789b])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  linarith only [hlam, hc378yz, htr389b, htr3910a, htr789a, htr8910a])
                obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc378yz, htr389a, htr479c, htr4910a, htr789c, htr8910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc378yz, htr389a, htr789c, htr7910a, htr8910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                  linarith only [hlam, hd12a, hd910b, htr124a, htr247a, htr479a, htr7910a])
                obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
                have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr249a, htr249b, htr249c, _, _⟩
                  linarith only [hlam, hd34a, hd910b, htr247a, htr249a, htr347a, htr4910a])
                obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hd34a, hd910b, htr346a, htr467a, htr679a, htr7910a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                rcases m.htr 2 4 6 (by decide) (by decide) with
                  ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
                ·
                  linarith only [hlam, hc346yz, htr246a, htr249a, htr367a, htr467b, htr479b]
                ·
                  linarith only [hlam, hd36a, hd45b, htr245a, htr246a, htr367a, htr467a]
            ·
              have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                linarith only [hlam, hc236zy, htr267a, htr367b, htr378a, htr678a])
              obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
              have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                linarith only [hlam, hc367yz, htr267a, htr268a, htr378a, htr678b])
              obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hc367yz, htr378a, htr467a, htr468a, htr678b])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                linarith only [hlam, hc367yz, htr268c, htr289a, htr378a, htr678c, htr789a])
              obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
              have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                linarith only [hlam, htr268b, htr269c, htr289b])
              obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc367yz, htr378a, htr678c, htr689a, htr789a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr246a, htr246b, htr246c, _, _⟩
                linarith only [hlam, hd12a, hd89b, htr124a, htr246a, htr468a, htr689a])
              obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hd12a, hd910b, htr126a, htr268a, htr689a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd12a, hd89b, htr126a, htr269a, htr6910a, htr8910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 6 7 9 (by decide) (by decide) with
                ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
              ·
                have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr247a, htr247b, htr247c, _, _⟩
                  linarith only [hlam, hd34a, hd79b, htr246a, htr247a, htr346a, htr467c, htr679a])
                obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
                rcases m.htr 4 7 8 (by decide) (by decide) with
                  ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
                ·
                  linarith only [hlam, hd34a, hd79b, htr347a, htr478a, htr678a, htr679a]
                ·
                  linarith only [hlam, hd37a, hd45b, htr245a, htr247a, htr378a, htr478a]
              ·
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc367yz, htr379a, htr679c, htr6910a, htr7910a]
                ·
                  linarith only [hlam, hc367yz, htr379b, htr3910a, htr679a, htr7910a]
  ·
    rcases m.htr 2 4 6 (by decide) (by decide) with
      ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
    ·
      rcases m.htr 4 6 7 (by decide) (by decide) with
        ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
      ·
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc023xy, hc367yz, htr024a, htr035a, htr135a, htr137a, htr246a, htr467a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr246a, htr248a, htr348a, htr467a])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12a, hd78b, htr124a, htr246a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr134a, htr137a, htr378a, htr678a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc023xy, hc567yz, htr024a, htr035a, htr246a, htr357c, htr378a, htr467a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc012yx, hc678zy, htr015a, htr024a, htr157a, htr246a, htr468a, htr578a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc346yz, htr136a, htr138a, htr368c, htr468a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hc789xy, htr137a, htr138a, htr378b, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd23b, hd89a, htr135a, htr138a, htr235a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc023xy, hc567yz, htr024a, htr035a, htr246a, htr357c, htr379a, htr467a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc012yx, hc789yz, htr015a, htr024a, htr157a, htr248a, htr489a, htr579a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc346yz, htr368a, htr468c, htr489a, htr689a]
        ·
          linarith only [hlam, hc346yz, htr368b, htr389a, htr468a, htr689a]
      ·
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc346yz, htr136a, htr137a, htr367c, htr467a])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc346yz, htr246a, htr247a, htr367a, htr467b])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr135a, htr137a, htr235a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd23b, hd79a, htr135a, htr137a, htr235a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc346yz, htr367a, htr467c, htr478a, htr678a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc023xy, hc378yz, htr024a, htr035a, htr135a, htr138a, htr247a, htr478a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc346yz, htr367b, htr379a, htr467a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc346yz, htr367a, htr467c, htr479a, htr679a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc012yx, hc789zy, htr015a, htr024a, htr158a, htr247a, htr479a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc023xy, hc578yz, htr024a, htr035a, htr247a, htr358c, htr389a, htr478a, htr589a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd89b, htr124a, htr247a, htr478a, htr789a]
        ·
          linarith only [hlam, hd34a, hd78b, htr134a, htr138a, htr389a, htr789a]
    ·
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd36a, hd45b, htr245a, htr246a, htr367a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr267a, htr267b, htr267c, _, _⟩
        linarith only [hlam, hc456yx, htr245a, htr246c, htr267a, htr467a])
      obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hd36a, hd45b, htr245a, htr246a, htr368a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr268a, htr268b, htr268c, _, _⟩
        linarith only [hlam, hc456yx, htr245a, htr246c, htr268a, htr468a])
      obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hd36a, hd45b, htr245a, htr246a, htr369a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr269a, htr269b, htr269c, _, _⟩
        linarith only [hlam, hc456yx, htr245a, htr246c, htr269a, htr469a])
      obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
      rcases m.htr 2 4 7 (by decide) (by decide) with
        ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
      ·
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd34a, hd78b, htr246a, htr247a, htr346a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd34a, hd79b, htr246a, htr247a, htr346a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hd34a, hd710b, htr246a, htr247a, htr346a, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, htr467c, htr479a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr248a, htr248b, htr248c, _, _⟩
            linarith only [hlam, hc457zy, htr247a, htr248a, htr478b, htr578a])
          obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd34a, hd89b, htr246a, htr248a, htr346a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hd34a, hd810b, htr246a, htr248a, htr346a, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hc457zy, htr478c, htr489a, htr578a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, hc457zy, htr358b, htr389a, htr478a, htr578b, htr789a])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr138a, htr138b, htr138c, _, _⟩
            linarith only [hlam, hd23b, hd89a, htr135a, htr138a, htr235a, htr389a])
          obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
          have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
            linarith only [hlam, hd34a, hd48b, htr134a, htr138a, htr3810a, htr4810a])
          obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc457zy, htr478a, htr578b, htr589a, htr789a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
            linarith only [hlam, hd23b, hd89a, htr238a, htr3810a, htr5810a, htr589a])
          obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc012yx, hc8910yz, htr015a, htr026a, htr158a, htr269a, htr5810a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            linarith only [hlam, hd23b, hd910a, htr235a, htr358a, htr589a, htr8910a])
          obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd23b, hd89a, htr235a, htr359a, htr5910a, htr8910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          rcases m.htr 7 9 10 (by decide) (by decide) with
            ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          ·
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hc367yz, htr379a, htr679c, htr6910a, htr7910a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr137a, htr137b, htr137c, _, _⟩
              linarith only [hlam, hd23b, hd79a, htr135a, htr137a, htr235a, htr379a])
            obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd34a, hd47b, htr134a, htr137a, htr378a, htr478a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            rcases m.htr 5 7 9 (by decide) (by decide) with
              ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
            ·
              linarith only [hlam, hc567yz, htr579a, htr679c, htr6910a, htr7910a]
            ·
              linarith only [hlam, hd23b, hd79a, htr237a, htr378a, htr578a, htr579a]
          ·
            rcases m.htr 5 7 9 (by decide) (by decide) with
              ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
            ·
              linarith only [hlam, hc457zy, htr479a, htr579b, htr5910a, htr7910a]
            ·
              linarith only [hlam, hd23b, hd89a, htr235a, htr357a, htr579a, htr7910a, htr8910a]
        ·
          have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr137a, htr137b, htr137c, _, _⟩
            linarith only [hlam, hd23b, hd78a, htr135a, htr137a, htr235a, htr357b, htr578a])
          obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, hd34a, hd47b, htr134a, htr137a, htr379a, htr479a])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, hd34a, hd47b, htr134a, htr137a, htr3710a, htr4710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd23b, hd78a, htr237a, htr379a, htr578a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hd23b, hd78a, htr237a, htr3710a, htr5710a, htr578a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hc012yx, hc789yz, htr015a, htr026a, htr157a, htr268a, htr579a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hc012yx, hc7910yz, htr015a, htr026a, htr157a, htr269a, htr5710a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd23b, hd89a, htr235a, htr357a, htr578a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hd23b, hd910a, htr235a, htr357a, htr579a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
          ·
            linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
      ·
        have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr137a, htr137b, htr137c, _, _⟩
          linarith only [hlam, hc234zy, htr134a, htr137a, htr247a, htr347c])
        obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr135a, htr137a, htr235a, htr378a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
          linarith only [hlam, hd23b, hd79a, htr135a, htr137a, htr235a, htr379a])
        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd37a, hd45b, htr245a, htr247a, htr378a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd37a, hd45b, htr245a, htr247a, htr379a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
          linarith only [hlam, hc457yx, htr245a, htr247c, htr279a, htr479a])
        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc023xy, hc367yz, htr027a, htr035a, htr135a, htr137a, htr278a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr138a, htr138b, htr138c, _, _⟩
          linarith only [hlam, hc023xy, hc378yz, htr026a, htr035a, htr135a, htr138a, htr267a, htr678a])
        obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc234zy, htr134a, htr138a, htr248a, htr348c])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd34a, hd89b, htr246a, htr248a, htr346a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd34a, hd48b, htr134a, htr138a, htr389a, htr489a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc023xy, hc578yz, htr026a, htr035a, htr267a, htr358c, htr389a, htr589a, htr678a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc012yx, hc789zy, htr015a, htr026a, htr158a, htr267a, htr589a, htr679a]
        ·
          linarith only [hlam, hc023xy, hc367yz, htr027a, htr035a, htr135a, htr137a, htr279a, htr679a]

theorem shard_474 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr347c : m.d 3 7 < m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348c : m.d 3 8 < m.d 4 8)
    : False :=
  proof_shard_474 m htr013b htr015a htr017a htr018a htr024a htr026a htr027a htr034c htr124a htr126a htr127a htr134a htr135a htr135b htr135c htr136a htr136c htr235a htr237a htr238a htr245a htr346a htr347a htr347c htr348a htr348c

#print axioms shard_474
end Jsp404.NoSatElevenDBMTerminal
