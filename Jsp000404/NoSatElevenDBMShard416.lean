import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_416 {lam p : ℝ} (m : ElevenModel lam p)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr037c : m.d 0 7 < m.d 3 7)
    (htr038c : m.d 0 8 < m.d 3 8)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348b : m.d 3 4 < m.d 3 8)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd13a := (m.hrange 1 3 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
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
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
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
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr035c, htr056a, htr345c, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, htr245c, htr256a, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd13a, hd67b, htr134a, htr345a, htr456a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd13a, hd68b, htr134a, htr345a, htr456a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  rcases m.htr 4 5 7 (by decide) (by decide) with
    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr035c, htr057a, htr345c, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd13a, hd78b, htr134a, htr345a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd13a, hd79b, htr134a, htr345a, htr457a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd13a, hd89b, htr134a, htr345a, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      rcases m.htr 3 6 7 (by decide) (by decide) with
        ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
      ·
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, htr036c, htr067a, htr367a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, hc123yz, htr134a, htr236c, htr267a, htr346b, htr367a])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr259a, htr259b, htr259c, _, _⟩
          linarith only [hlam, hc569yx, htr256b, htr259a, htr267a, htr567a])
        obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hd12a, hd56b, htr125a, htr259a, htr456a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd13a, hd910b, htr134a, htr345a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd13a, hd57b, htr134a, htr346b, htr367a, htr578a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc056yz, htr067b, htr078a, htr567a, htr678a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd13a, hd57b, htr134a, htr346b, htr367a, htr579a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc123yz, hc589zy, htr037c, htr078a, htr134a, htr237a, htr345a, htr459a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc123yz, hc578zy, htr134a, htr238a, htr345a, htr389a, htr458a, htr789a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd13a, hd56b, htr134a, htr348b, htr389a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc056yz, htr068a, htr568c, htr589a, htr689a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, hc568zy, htr068a, htr069a, htr589a, htr689c])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd56b, hd910a, htr036c, htr069a, htr367a, htr567a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc578zy, htr589a, htr679b, htr6910a, htr789b, htr8910a]
      ·
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc023yz, htr036b, htr067a, htr236a, htr367a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc123yz, hc578zy, htr134a, htr236a, htr345a, htr367a, htr458a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc567zy, htr067a, htr068a, htr578a, htr678c])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc123yz, hc567zy, htr037c, htr078a, htr134a, htr237a, htr345a, htr457a, htr678a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc579yx, htr057b, htr059a, htr078a, htr578a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc023yz, htr035b, htr059a, htr235a, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hd13a, hd56b, htr134a, htr345b, htr359a, htr456a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc123yz, hc589zy, htr036c, htr068a, htr134a, htr236a, htr345a, htr459a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a]
        ·
          linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a]
    ·
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hd13a, hd56b, htr134a, htr345b, htr358a, htr456a, htr458a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc023yz, htr035b, htr058a, htr235a, htr358a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, hc568yx, htr056b, htr058a, htr067a, htr567a])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, hc578yx, htr057b, htr058a, htr079a, htr579a])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc567zy, htr457a, htr458a, htr578b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc123yz, hc567zy, htr037c, htr079a, htr134a, htr237a, htr345a, htr457a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc123yz, hc789yz, htr036c, htr067a, htr134a, htr236a, htr348a, htr489a, htr679a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc568yx, htr456a, htr458c, htr489a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a]
      ·
        linarith only [hlam, hd23b, hd89a, htr036c, htr067a, htr236a, htr678a, htr789a]
  ·
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd13a, hd56b, htr134a, htr345b, htr357a, htr456a, htr457a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc023yz, htr035b, htr057a, htr235a, htr357a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr068a, htr068b, htr068c, _, _⟩
      linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
    obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr035c, htr058a, htr345c, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr057c, htr058b, htr078c])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc567yx, htr057b, htr078a, htr456a, htr457c, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc123yz, hc789yx, htr134a, htr235a, htr347a, htr357a, htr478a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc567yx, htr456a, htr457c, htr479a, htr579a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd13a, hd89b, htr134a, htr345a, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
        linarith only [hlam, hc578xy, htr057a, htr058b, htr089a, htr589a])
      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc123yz, hc568zy, htr038c, htr089a, htr134a, htr238a, htr345a, htr458a, htr689a]
      ·
        linarith only [hlam, hc123yz, hc789zy, htr036c, htr068a, htr134a, htr236a, htr347a, htr479a, htr689a]
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc567yx, htr057a, htr058a, htr456a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      rcases m.htr 4 5 9 (by decide) (by decide) with
        ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
      ·
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, htr035c, htr059a, htr345c, htr459a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr057c, htr059b, htr079c])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, htr058c, htr059b, htr089c])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc567yx, htr057b, htr079a, htr456a, htr457c, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc568yx, htr058b, htr089a, htr456a, htr458c, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc123yz, hc789xy, htr134a, htr235a, htr347a, htr357a, htr479a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd13a, hd89b, htr134a, htr347a, htr478a, htr789a]
        ·
          linarith only [hlam, hd13a, hd78b, htr134a, htr348a, htr489a, htr789a]
      ·
        rcases m.htr 4 5 10 (by decide) (by decide) with
          ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
        ·
          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
            linarith only [hlam, htr035c, htr0510a, htr345c, htr4510a])
          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0510b, htr057c, htr0710c])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
            linarith only [hlam, htr0510b, htr058c, htr0810c])
          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, hc567yx, htr057b, htr0710a, htr456a, htr457c, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc568yx, htr058b, htr0810a, htr456a, htr458c, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc123yz, hc7810xy, htr134a, htr235a, htr347a, htr357a, htr4710a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd13a, hd810b, htr134a, htr347a, htr478a, htr7810a]
          ·
            linarith only [hlam, hd13a, hd78b, htr134a, htr348a, htr4810a, htr7810a]
        ·
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hc123yz, hc789yx, htr134a, htr235a, htr347a, htr357a, htr478a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc567yx, htr456a, htr457c, htr479a, htr579a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc123yz, hc789zy, htr035c, htr058a, htr134a, htr235a, htr347a, htr479a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hc568yx, htr456a, htr458c, htr489a, htr589a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd13a, hd89b, htr134a, htr347a, htr478a, htr789a]
            ·
              linarith only [hlam, hd13a, hd78b, htr134a, htr348a, htr489a, htr789a]
          ·
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc123yz, hc789xy, htr134a, htr235a, htr347a, htr357a, htr479a, htr578a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hc567yx, htr456a, htr457c, htr479a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hc123yz, hc789yz, htr134a, htr235a, htr348a, htr357a, htr489a, htr579a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc568yx, htr456a, htr458c, htr489a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a]
            ·
              linarith only [hlam, hd56b, hd89a, htr456a, htr457a, htr578a, htr789a]

theorem shard_416 {lam p : ℝ} (m : ElevenModel lam p)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr037c : m.d 0 7 < m.d 3 7)
    (htr038c : m.d 0 8 < m.d 3 8)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236c : m.d 2 6 < m.d 2 3)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    (htr245c : m.d 2 5 < m.d 4 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    (htr348b : m.d 3 4 < m.d 3 8)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    : False :=
  proof_shard_416 m htr035b htr035c htr036b htr036c htr037c htr038c htr125a htr134a htr235a htr236a htr236c htr237a htr238a htr245c htr345a htr345b htr345c htr346b htr347a htr348a htr348b htr456a

#print axioms shard_416
end Jsp404.NoSatElevenDBMTerminal
