import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_030 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr239a : m.d 3 9 + lam ≤ m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr248b : m.d 4 8 < m.d 2 8)
    (htr248c : m.d 2 8 < m.d 2 4)
    (htr249b : m.d 4 9 < m.d 2 9)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr258a : m.d 5 8 + lam ≤ m.d 2 5)
    (htr259a : m.d 5 9 + lam ≤ m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  have hd36a := (m.hrange 3 6 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
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
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc057xy, hc057yx, hc057yz, hc057zy⟩ := endpoint_caps m 0 5 7 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc378xy, hc378yx, hc378yz, hc378zy⟩ := endpoint_caps m 3 7 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc489xy, hc489yx, hc489yz, hc489zy⟩ := endpoint_caps m 4 8 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hd24b, hd36a, htr034a, htr036a, htr245a, htr345a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, hd23b, hd46a, htr034a, htr035a, htr235a, htr346a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hd23b, hd46a, htr034a, htr037a, htr237a, htr346a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, hd23b, hd46a, htr034a, htr038a, htr238a, htr346a])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr039a, htr039b, htr039c, _, _⟩
    linarith only [hlam, hd23b, hd46a, htr034a, htr039a, htr239a, htr346a])
  obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc234zy, htr245c, htr257a, htr345a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hd24b, hd56a, htr245a, htr356a, htr357a, htr457a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc234zy, htr245c, htr258a, htr345a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hd24b, hd56a, htr245a, htr356a, htr358a, htr458a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc234zy, htr245c, htr259a, htr345a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hd24b, hd56a, htr245a, htr356a, htr359a, htr459a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd24b, hd67a, htr245a, htr345a, htr346a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd23b, hd46a, htr123a, htr126a, htr267a, htr467a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc236yx, htr016c, htr067a, htr123a, htr126c, htr267a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc236yx, htr123a, htr126c, htr167a, htr267a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hd24b, hd68a, htr245a, htr345a, htr346a, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd23b, hd46a, htr123a, htr126a, htr268a, htr468a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hc236yx, htr123a, htr126c, htr168a, htr268a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hd24b, hd69a, htr245a, htr345a, htr346a, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd23b, hd46a, htr123a, htr126a, htr269a, htr469a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, hc236yx, htr016c, htr069a, htr123a, htr126c, htr269a])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, hc236yx, htr123a, htr126c, htr169a, htr269a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  rcases m.htr 3 4 7 (by decide) (by decide) with
    ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
  ·
    have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr127a, htr127b, htr127c, _, _⟩
      linarith only [hlam, hc234zy, htr124a, htr127a, htr247b, htr347a])
    obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
    rcases m.htr 3 4 8 (by decide) (by decide) with
      ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
    ·
      have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr128a, htr128b, htr128c, _, _⟩
        linarith only [hlam, hc234zy, htr124a, htr128a, htr248b, htr348a])
      obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
      rcases m.htr 0 4 5 (by decide) (by decide) with
        ⟨htr045a, htr045b, htr045c, _, _⟩ | ⟨htr045a, htr045b, htr045c, _, _⟩
      ·
        have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr026a, htr026b, htr026c, _, _⟩
          linarith only [hlam, hc246yx, htr024b, htr026a, htr045a, htr245a])
        obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
        have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr278a, htr278b, htr278c, _, _⟩
          linarith only [hlam, hd02a, hd78b, htr026a, htr126a, htr127a, htr278a])
        obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc234zy, htr247c, htr278a, htr347a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc234zy, htr247a, htr347b, htr378a, htr478a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          linarith only [hlam, hc023xy, hc257zy, htr026a, htr037a, htr126a, htr127a, htr378a, htr578a]
        ·
          linarith only [hlam, hc023xy, hc278zy, htr026a, htr035a, htr126a, htr128a, htr357a, htr578a]
      ·
        have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr047a, htr047b, htr047c, _, _⟩
          linarith only [hlam, htr045a, htr047a, htr457c])
        obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr045a, htr048a, htr458c])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr049a, htr049b, htr049c, _, _⟩
          linarith only [hlam, htr045a, htr049a, htr459c])
        obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
        rcases m.htr 3 4 9 (by decide) (by decide) with
          ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
        ·
          have hforced129 := (m.htr 1 2 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr129a, htr129b, htr129c, _, _⟩
            linarith only [hlam, hc234zy, htr124a, htr129a, htr249b, htr349a])
          obtain ⟨htr129a, htr129b, htr129c, _, _⟩ := hforced129
          rcases m.htr 0 2 6 (by decide) (by decide) with
            ⟨htr026a, htr026b, htr026c, _, _⟩ | ⟨htr026a, htr026b, htr026c, _, _⟩
          ·
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, hd02a, hd78b, htr026a, htr126a, htr127a, htr278a])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, hc234zy, htr247c, htr278a, htr347a, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              linarith only [hlam, hc024xy, hc257zy, htr026a, htr045a, htr126a, htr127a, htr457c, htr478a, htr578a]
            ·
              linarith only [hlam, hc023xy, hc278zy, htr026a, htr035a, htr126a, htr128a, htr357a, htr578a]
          ·
            rcases m.htr 3 4 10 (by decide) (by decide) with
              ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
            ·
              rcases m.htr 4 7 8 (by decide) (by decide) with
                ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
              ·
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, hc234zy, htr247c, htr278a, htr347a, htr478a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, htr347c, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd46a, hd89b, htr346a, htr347a, htr478a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hd46a, hd78b, htr346a, htr348a, htr489a, htr789a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc246yx, hc578yz, htr126a, htr127a, htr248a, htr278a, htr489a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, hc246yx, hc789zy, htr126a, htr127a, htr245a, htr279a, htr458a, htr589a])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                  linarith only [hlam, hc246yx, hc8910xy, htr126a, htr128a, htr245a, htr2810a, htr458a, htr589a])
                obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, hd46a, hd78b, htr278a, htr279a, htr346a, htr347b, htr379a])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                  linarith only [hlam, hc268xy, hc789yx, htr126a, htr127a, htr278a, htr2810a, htr378b, htr379a, htr3810a])
                obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                  linarith only [hlam, hc236yx, hc578yz, htr126a, htr127a, htr238a, htr278a, htr3810a, htr5810a])
                obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                  linarith only [hlam, hc246yx, hc8910yz, htr126a, htr129a, htr245a, htr2910a, htr458a, htr5810a])
                obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc789yx, htr278a, htr279c, htr2910a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd78b, hd89a, htr278a, htr279a, htr7910a, htr8910a]
                ·
                  linarith only [hlam, hd24b, hd910a, htr245a, htr458a, htr589a, htr8910a]
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr047b, htr078a, htr478a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr278a, htr278b, htr278c, _, _⟩
                  linarith only [hlam, htr247b, htr278a, htr478a])
                obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                  linarith only [hlam, hc234zy, htr247a, htr347b, htr378a, htr478a])
                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                rcases m.htr 5 7 8 (by decide) (by decide) with
                  ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
                ·
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd24b, hd79a, htr247a, htr478a, htr578a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
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
                    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                      linarith only [hlam, hd46a, hd79b, htr048b, htr089a, htr267c, htr278c, htr289a, htr346a, htr348a, htr679a])
                    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, htr237b, htr267c, htr379a, htr679a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                    have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      linarith only [hlam, hc246yx, hc8910yx, htr126a, htr128a, htr247a, htr289a, htr478a, htr7810a])
                    obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                    have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                      linarith only [hlam, hc057zy, htr078c, htr0810a, htr578a, htr7810a])
                    obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                    have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                      linarith only [hlam, hd46a, hd79b, htr048b, htr0810a, htr267c, htr278c, htr2810a, htr346a, htr348a, htr679a])
                    obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                    have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                      linarith only [hlam, hc246yx, hc8910zy, htr126a, htr128a, htr245a, htr2810a, htr459a, htr5910a])
                    obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                    have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                      linarith only [hlam, hc013xy, hc579yz, htr016a, htr039a, htr167a, htr3910a, htr5910a, htr679a])
                    obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd46a, hd910b, htr048b, htr089a, htr346a, htr348a, htr8910a]
                    ·
                      linarith only [hlam, hd57a, hd89b, htr378a, htr379b, htr3910a, htr578a, htr8910a]
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, hc567yz, htr047b, htr079a, htr478a, htr578a, htr679a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                      linarith only [hlam, hc567yz, htr378a, htr379a, htr578a, htr679a])
                    obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
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
                      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                        linarith only [hlam, hd46a, hd710b, htr048b, htr0810a, htr267c, htr278c, htr2810a, htr346a, htr348a, htr6710a])
                      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hc246yx, hc8910xy, htr126a, htr128a, htr247a, htr2810a, htr478a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                        linarith only [hlam, hc057zy, htr078c, htr089a, htr578a, htr789a])
                      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd46a, hd910b, htr048b, htr089a, htr346a, htr348a, htr8910a]
                      ·
                        linarith only [hlam, hd46a, hd89b, htr049b, htr0910a, htr346a, htr349a, htr8910a]
                    ·
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, hc057zy, htr078c, htr089a, htr578a, htr789a])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                          linarith only [hlam, hc257zy, htr278c, htr289a, htr578a, htr789a])
                        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc246yx, hc8910yx, htr126a, htr128a, htr247a, htr289a, htr478a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, hc057zy, htr078c, htr0810a, htr578a, htr7810a])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                          linarith only [hlam, hd46a, hd89b, htr048b, htr0810a, htr2810a, htr289a, htr346a, htr348a])
                        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                          linarith only [hlam, hc246yx, hc8910zy, htr126a, htr128a, htr245a, htr2810a, htr459a, htr5910a])
                        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
                          linarith only [hlam, hc236yx, hc589yz, htr126a, htr128a, htr239a, htr289a, htr3910a, htr5910a])
                        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
                        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                          linarith only [hlam, hc567yz, htr069c, htr0910a, htr379b, htr3910a, htr579a, htr679c])
                        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd46a, hd910b, htr048b, htr089a, htr346a, htr348a, htr8910a]
                        ·
                          linarith only [hlam, hd46a, hd89b, htr049b, htr0910a, htr346a, htr349a, htr8910a]
                      ·
                        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
                          linarith only [hlam, hc246yx, hc8910xy, htr126a, htr128a, htr247a, htr2810a, htr478a, htr789a])
                        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
                        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                          linarith only [hlam, hc257zy, htr278c, htr2810a, htr378b, htr3810a, htr578a])
                        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                          linarith only [hlam, hd24b, hd58a, htr247a, htr478a, htr589a, htr789a])
                        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                          linarith only [hlam, hd23b, hd89a, htr238a, htr3810a, htr5810a, htr589a])
                        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                          linarith only [hlam, hc246yx, hc8910yz, htr126a, htr129a, htr245a, htr2910a, htr458a, htr5810a])
                        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hc567yz, htr269c, htr2910a, htr579a, htr679c, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd23b, hd89a, htr237a, htr379a, htr7910a, htr8910a]
                        ·
                          linarith only [hlam, hd24b, hd910a, htr247a, htr478a, htr789a, htr8910a]
                ·
                  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                    linarith only [hlam, hc246yx, hc789xy, htr126a, htr127a, htr245a, htr279a, htr457a, htr578a])
                  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                  have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                    linarith only [hlam, hc246yx, hc7810xy, htr126a, htr127a, htr245a, htr2710a, htr457a, htr578a])
                  obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc234zy, htr247c, htr279a, htr347a, htr479a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, hc234zy, htr247c, htr2710a, htr347a, htr4710a])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd24b, hd78a, htr247a, htr479a, htr578a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                    linarith only [hlam, hc246yx, hc789yz, htr126a, htr128a, htr245a, htr289a, htr457a, htr579a])
                  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc234zy, htr248c, htr289a, htr348a, htr489a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, hd24b, hd78a, htr247a, htr4710a, htr5710a, htr578a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
                    linarith only [hlam, hc246yx, hc7910yz, htr126a, htr129a, htr245a, htr2910a, htr457a, htr5710a])
                  obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd24b, hd89a, htr245a, htr457a, htr578a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd24b, hd910a, htr245a, htr457a, htr579a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hc278zy, htr289c, htr2910a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hd24b, hd79a, htr248a, htr489a, htr7910a, htr8910a]
            ·
              have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                linarith only [hlam, htr3410c, htr347b, htr3710b])
              obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
              have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                linarith only [hlam, htr3410c, htr348b, htr3810b])
              obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
              have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                linarith only [hlam, htr347c, htr3710a, htr4710a])
              obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc7810yx, htr3410a, htr347a, htr4710b, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, htr348c, htr3810a, htr4810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                linarith only [hlam, hd24b, hd57a, htr245a, htr3410a, htr345a, htr4710b, htr5710a])
              obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hd24b, hd710a, htr247a, htr478a, htr5710a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              rcases m.htr 7 8 10 (by decide) (by decide) with
                ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              ·
                linarith only [hlam, hd24b, hd78a, htr245a, htr3410a, htr345a, htr4810b, htr7810a]
              ·
                linarith only [hlam, hd24b, hd810a, htr245a, htr457a, htr578a, htr7810a]
        ·
          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
            linarith only [hlam, htr347b, htr349c, htr379b])
          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
            linarith only [hlam, htr348b, htr349c, htr389b])
          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, htr347c, htr379a, htr479a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc789yx, htr347a, htr349a, htr478a, htr479b])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, htr348c, htr389a, htr489a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hd24b, hd57a, htr245a, htr345a, htr349a, htr479b, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hd24b, hd79a, htr247a, htr478a, htr578a, htr579a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd24b, hd78a, htr245a, htr345a, htr349a, htr489b, htr789a]
          ·
            linarith only [hlam, hd24b, hd89a, htr245a, htr457a, htr578a, htr789a]
    ·
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr347b, htr348c, htr378b])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, htr347c, htr378a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc789xy, htr347a, htr348a, htr478b, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hc7810xy, htr347a, htr348a, htr4710a, htr478b])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd24b, hd89a, htr245a, htr345a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd24b, hd57a, htr245a, htr345a, htr348a, htr478b, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd24b, hd78a, htr247a, htr479a, htr578a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hd24b, hd78a, htr247a, htr4710a, htr5710a, htr578a])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc013xy, hc789yz, htr016a, htr035a, htr168a, htr357a, htr579a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr349a, htr349b, htr349c, _, _⟩
        linarith only [hlam, hc468yz, htr348a, htr349a, htr489c, htr689a])
      obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
        linarith only [hlam, hd24b, hd910a, htr245a, htr345a, htr349a, htr4910a])
      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc013xy, hc7910yz, htr016a, htr035a, htr169a, htr357a, htr5710a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hc468yz, htr489a, htr689c, htr6910a, htr8910a]
      ·
        linarith only [hlam, hc468yz, htr489b, htr4910a, htr689a, htr8910a]
  ·
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd24b, hd78a, htr245a, htr345a, htr347a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd24b, hd79a, htr245a, htr345a, htr347a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, htr457b, htr479a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr016a, htr167a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        linarith only [hlam, hd01a, hd810b, htr016a, htr167a, htr678a, htr7810a])
      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc013xy, hc789zy, htr016a, htr035a, htr167a, htr358a, htr589a, htr679a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc013xy, hc578yz, htr016a, htr038a, htr167a, htr389a, htr589a, htr678a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd01a, hd910b, htr016a, htr167a, htr679a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          linarith only [hlam, hc578yz, htr589a, htr789c, htr7910a, htr8910a])
        obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc578yz, htr459b, htr4910a, htr589b, htr789a, htr8910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr349a, htr349b, htr349c, _, _⟩
          linarith only [hlam, hd24b, hd910a, htr245a, htr345a, htr349a, htr4910a])
        obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          linarith only [hlam, hc013xy, hc7910zy, htr016a, htr035a, htr167a, htr359a, htr5910a, htr6710a])
        obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hc378yz, htr3810a, htr6710a, htr678a, htr7810b])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd24b, hd810a, htr248a, htr3810a, htr389a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 3 4 8 (by decide) (by decide) with
          ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
        ·
          linarith only [hlam, hd46a, hd78b, htr346a, htr348a, htr489a, htr789a]
        ·
          linarith only [hlam, hc478yz, htr348a, htr349a, htr489c, htr789a]
      ·
        have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr349a, htr349b, htr349c, _, _⟩
          linarith only [hlam, hc467yz, htr347a, htr349a, htr479c, htr679a])
        obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc378yz, htr389a, htr678a, htr679a, htr789b])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc478yz, htr489a, htr678a, htr679a, htr789b])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hd24b, hd89a, htr245a, htr345a, htr348a, htr489a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hd46a, hd78b, htr346a, htr348a, htr4810a, htr7810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
          linarith only [hlam, hd24b, hd89a, htr248a, htr3810a, htr389a, htr4810a])
        obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd24b, hd910a, htr245a, htr345a, htr349a, htr4910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc013xy, hc578yz, htr016a, htr038a, htr167a, htr3810a, htr5810a, htr678a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc013xy, hc8910yz, htr016a, htr035a, htr169a, htr358a, htr5810a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a]
        ·
          linarith only [hlam, hc467yz, htr479b, htr4910a, htr679a, htr7910a]
    ·
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc467yz, htr347a, htr348a, htr478c, htr678a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd24b, hd89a, htr245a, htr345a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
        linarith only [hlam, hd24b, hd810a, htr245a, htr345a, htr348a, htr4810a])
      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        linarith only [hlam, hc467yz, htr478b, htr4810a, htr678a, htr7810a])
      obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hc467yz, htr478a, htr678c, htr6810a, htr7810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
        linarith only [hlam, hc013xy, hc8910zy, htr016a, htr035a, htr168a, htr359a, htr5910a, htr6810a])
      obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
      have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        linarith only [hlam, hd01a, hd910b, htr016a, htr168a, htr689a, htr8910a])
      obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd01a, hd89b, htr016a, htr169a, htr6910a, htr8910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        rcases m.htr 0 4 5 (by decide) (by decide) with
          ⟨htr045a, htr045b, htr045c, _, _⟩ | ⟨htr045a, htr045b, htr045c, _, _⟩
        ·
          have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr026a, htr026b, htr026c, _, _⟩
            linarith only [hlam, hc246yx, htr024b, htr026a, htr045a, htr245a])
          obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
          have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr127a, htr127b, htr127c, _, _⟩
            linarith only [hlam, hd02a, hd79b, htr026a, htr126a, htr127a, htr267c, htr679a])
          obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
          rcases m.htr 2 7 8 (by decide) (by decide) with
            ⟨htr278a, htr278b, htr278c, _, _⟩ | ⟨htr278a, htr278b, htr278c, _, _⟩
          ·
            linarith only [hlam, hd02a, hd79b, htr026a, htr267b, htr278a, htr678a, htr679a]
          ·
            linarith only [hlam, hd23b, hd47a, htr123a, htr127a, htr278a, htr478a]
        ·
          have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr349a, htr349b, htr349c, _, _⟩
            linarith only [hlam, hc014xy, hc489yz, htr016a, htr045a, htr168a, htr345a, htr349a, htr689a])
          obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
          rcases m.htr 4 9 10 (by decide) (by decide) with
            ⟨htr4910a, htr4910b, htr4910c, _, _⟩ | ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          ·
            linarith only [hlam, hd46a, hd89b, htr346a, htr349a, htr4910a, htr8910a]
          ·
            linarith only [hlam, hc014xy, hc589yz, htr016a, htr045a, htr168a, htr459c, htr4910a, htr5910a, htr689a]
      ·
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a]
        ·
          linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a]

theorem shard_030 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr024b : m.d 0 2 < m.d 0 4)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126c : m.d 1 6 < m.d 1 2)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr237b : m.d 3 7 < m.d 2 7)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr239a : m.d 3 9 + lam ≤ m.d 2 3)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr248b : m.d 4 8 < m.d 2 8)
    (htr248c : m.d 2 8 < m.d 2 4)
    (htr249b : m.d 4 9 < m.d 2 9)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr258a : m.d 5 8 + lam ≤ m.d 2 5)
    (htr259a : m.d 5 9 + lam ≤ m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    : False :=
  proof_shard_030 m htr016a htr016c htr024b htr036a htr123a htr124a htr126a htr126c htr235a htr237a htr237b htr238a htr239a htr245a htr245c htr247a htr247b htr247c htr248a htr248b htr248c htr249b htr257a htr258a htr259a htr345a htr346a htr356a

#print axioms shard_030
end Jsp404.NoSatElevenDBMTerminal
