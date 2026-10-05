import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_200 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr046a : m.d 0 4 + lam ≤ m.d 4 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr057a : m.d 0 5 + lam ≤ m.d 5 7)
    (htr057b : m.d 0 5 < m.d 0 7)
    (htr058a : m.d 0 5 + lam ≤ m.d 5 8)
    (htr058b : m.d 0 5 < m.d 0 8)
    (htr059a : m.d 0 5 + lam ≤ m.d 5 9)
    (htr059b : m.d 0 5 < m.d 0 9)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
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
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc469xy, hc469yx, hc469yz, hc469zy⟩ := endpoint_caps m 4 6 9 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr034b, htr047a, htr347a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr046b, htr047c, htr067b])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, htr134b, htr147a, htr347a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, hc456xy, htr245a, htr247a, htr346a, htr347a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc456xy, htr046c, htr067a, htr245a, htr246b, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, htr046c, htr067a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hc678xy, htr034b, htr046a, htr347a, htr467b, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hc456xy, htr245a, htr246b, htr268a, htr468a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hc679xy, htr034b, htr046a, htr347a, htr467b, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  rcases m.htr 3 4 8 (by decide) (by decide) with
    ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
  ·
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc456xy, htr046a, htr048a, htr345a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, htr047c, htr048b, htr078c])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr248a, htr248b, htr248c, _, _⟩
      linarith only [hlam, htr234c, htr248a, htr348a])
    obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hc123zy, htr035b, htr057b, htr078a, htr134a, htr235a, htr347a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hc789yx, htr234c, htr247a, htr348a, htr478c, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
      linarith only [hlam, hc467yx, htr046a, htr047c, htr079a, htr479a])
    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc457yz, htr347a, htr348a, htr478c, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd23a, hd78b, htr035b, htr057b, htr079a, htr235a, htr578a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hc023zy, hc789zy, htr035b, htr036a, htr057a, htr235a, htr236c, htr268a, htr579a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hc012xy, hc678yz, htr015a, htr028a, htr157a, htr289a, htr578a, htr689a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc458xy, htr245a, htr248b, htr289a, htr489a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd23a, hd89b, htr035b, htr057a, htr235a, htr578a, htr789a]
    ·
      linarith only [hlam, hd23a, hd78b, htr234a, htr348a, htr489a, htr789a]
  ·
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, htr034b, htr048a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    rcases m.htr 3 4 9 (by decide) (by decide) with
      ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
    ·
      have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr049a, htr049b, htr049c, _, _⟩
        linarith only [hlam, hc456xy, htr046a, htr049a, htr345a, htr349a])
      obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, htr047c, htr049b, htr079c])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
        linarith only [hlam, htr048c, htr049b, htr089c])
      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc123zy, htr035b, htr057b, htr079a, htr134a, htr235a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc789xy, htr234c, htr247a, htr349a, htr478a, htr479c])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc467yx, htr046a, htr047c, htr078a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc123zy, htr035b, htr058b, htr089a, htr134a, htr235a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc457yz, htr347a, htr349a, htr479c, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd23a, hd79b, htr035b, htr057b, htr078a, htr235a, htr578a, htr579a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd23a, hd89b, htr035b, htr057a, htr235a, htr578a, htr789a]
      ·
        linarith only [hlam, hc478yz, htr348a, htr349a, htr489c, htr789a]
    ·
      have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr049a, htr049b, htr049c, _, _⟩
        linarith only [hlam, htr034b, htr049a, htr349a])
      obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
      rcases m.htr 3 4 10 (by decide) (by decide) with
        ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
      ·
        have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
          linarith only [hlam, hc456xy, htr0410a, htr046a, htr3410a, htr345a])
        obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
          linarith only [hlam, htr0410b, htr047c, htr0710c])
        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
          linarith only [hlam, htr0410b, htr048c, htr0810c])
        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hc123zy, htr035b, htr057b, htr0710a, htr134a, htr235a, htr347a, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc7810xy, htr234c, htr247a, htr3410a, htr4710c, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc467yx, htr046a, htr047c, htr078a, htr478a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hc123zy, htr035b, htr058b, htr0810a, htr134a, htr235a, htr348a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
          linarith only [hlam, hc457yz, htr3410a, htr347a, htr4710c, htr5710a])
        obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd23a, hd710b, htr035b, htr057b, htr078a, htr235a, htr5710a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd810b, htr035b, htr057a, htr235a, htr578a, htr7810a]
        ·
          linarith only [hlam, hc478yz, htr3410a, htr348a, htr4810c, htr7810a]
      ·
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd13b, hd67a, htr134a, htr347a, htr478a, htr678a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc467yx, htr046a, htr047c, htr078a, htr478a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc467yx, htr146a, htr147c, htr178a, htr478a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          rcases m.htr 5 7 8 (by decide) (by decide) with
            ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
          ·
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc123zy, hc789yx, htr035b, htr057a, htr134a, htr235a, htr347a, htr479a, htr578a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, hc467yx, htr046a, htr047c, htr079a, htr479a])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hc123zy, hc7810yx, htr035b, htr057a, htr134a, htr235a, htr347a, htr4710a, htr578a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, hc467yx, htr046a, htr047c, htr0710a, htr4710a])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd23a, hd78b, htr035b, htr057b, htr079a, htr235a, htr578a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hc123zy, hc789zy, htr035b, htr057a, htr134a, htr235a, htr348a, htr489a, htr579a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
              linarith only [hlam, hc468yx, htr046a, htr048c, htr089a, htr489a])
            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
            have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
              linarith only [hlam, hd23a, hd78b, htr035b, htr057b, htr0710a, htr235a, htr5710a, htr578a])
            obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hc123zy, hc7910zy, htr035b, htr057a, htr134a, htr235a, htr349a, htr4910a, htr5710a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hd23a, hd89b, htr035b, htr057a, htr235a, htr578a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hd23a, hd910b, htr035b, htr057a, htr235a, htr579a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd79b, htr035b, htr058b, htr089a, htr235a, htr7910a, htr8910a]
            ·
              linarith only [hlam, hc478yz, htr489b, htr4910a, htr789a, htr8910a]
          ·
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd23a, hd79b, htr035b, htr057b, htr078a, htr235a, htr578a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hc567zy, htr017c, htr079a, htr178a, htr578a, htr679a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              rcases m.htr 6 7 10 (by decide) (by decide) with
                ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              ·
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910yx, htr035b, htr057b, htr078a, htr134a, htr235a, htr348a, htr4810a, htr789a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                    linarith only [hlam, hc468yx, htr046a, htr048c, htr0810a, htr4810a])
                  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd23a, hd58b, htr035b, htr057b, htr078a, htr235a, htr589a, htr789a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                    linarith only [hlam, hd23a, hd89b, htr035b, htr058b, htr0810a, htr235a, htr5810a, htr589a])
                  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910zy, htr035b, htr058a, htr134a, htr235a, htr349a, htr4910a, htr5810a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hc567zy, htr469b, htr4910a, htr579a, htr679b, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd23a, hd910b, htr035b, htr057b, htr078a, htr235a, htr789a, htr8910a]
                  ·
                    linarith only [hlam, hd23a, hd89b, htr035b, htr057b, htr079a, htr235a, htr7910a, htr8910a]
                ·
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc567zy, htr468b, htr489a, htr578a, htr678b, htr789a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910xy, htr035b, htr057b, htr078a, htr134a, htr235a, htr348a, htr489a, htr7810a])
                  obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc567zy, htr468b, htr4810a, htr578a, htr678b, htr7810a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910yz, htr035b, htr059a, htr134a, htr235a, htr348a, htr4810a, htr5910a])
                  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                    linarith only [hlam, hc123zy, hc589zy, htr035b, htr059b, htr0910a, htr134a, htr235a, htr348a, htr489a, htr5910a])
                  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc469yx, htr046a, htr049c, htr0910a, htr4910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd13b, hd89a, htr134a, htr349a, htr4910a, htr8910a]
                  ·
                    linarith only [hlam, hd13b, hd910a, htr134a, htr348a, htr489a, htr8910a]
              ·
                have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                  linarith only [hlam, htr067b, htr0710a, htr6710a])
                obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0710c, htr078b, htr0810b])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                  linarith only [hlam, htr0710c, htr079b, htr0910b])
                obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc468yx, htr046a, htr048c, htr0810a, htr4810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc469yx, htr046a, htr049c, htr0910a, htr4910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc123zy, hc8910yx, htr035b, htr057b, htr078a, htr134a, htr235a, htr348a, htr4810a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc567zy, htr468b, htr489a, htr578a, htr678b, htr789a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd13b, hd89a, htr134a, htr349a, htr4910a, htr8910a]
                ·
                  linarith only [hlam, hd13b, hd910a, htr134a, htr348a, htr489a, htr8910a]
            ·
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, htr067b, htr079a, htr679a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, htr078b, htr079c, htr089b])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc468yx, htr046a, htr048c, htr089a, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc123zy, hc8910xy, htr035b, htr057b, htr078a, htr134a, htr235a, htr348a, htr489a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hc567zy, htr468b, htr4810a, htr578a, htr678b, htr7810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                linarith only [hlam, hc123zy, hc8910yz, htr035b, htr059a, htr134a, htr235a, htr348a, htr4810a, htr5910a])
              obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
              have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                linarith only [hlam, hc023zy, hc579zy, htr035b, htr036a, htr059b, htr0910a, htr235a, htr236c, htr267a, htr5910a, htr679a])
              obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd57b, hd89a, htr017c, htr079c, htr0910a, htr178a, htr578a, htr8910a]
              ·
                linarith only [hlam, hd13b, hd910a, htr134a, htr348a, htr489a, htr8910a]
        ·
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd12b, hd89a, htr126a, htr267a, htr678a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd13b, hd78a, htr134a, htr348a, htr489a, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
            linarith only [hlam, hc468yx, htr046a, htr048c, htr089a, htr489a])
          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc023zy, hc578zy, htr035b, htr036a, htr058b, htr089a, htr235a, htr236c, htr267a, htr589a, htr678a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc123zy, hc789yz, htr035b, htr058a, htr134a, htr235a, htr347a, htr479a, htr589a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc123zy, hc8910yx, htr035b, htr058a, htr134a, htr235a, htr348a, htr4810a, htr589a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
            linarith only [hlam, hc468yx, htr046a, htr048c, htr0810a, htr4810a])
          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
          have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
            linarith only [hlam, hc023zy, hc578zy, htr035b, htr036a, htr058b, htr0810a, htr235a, htr236c, htr267a, htr5810a, htr678a])
          obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hc123zy, hc8910zy, htr035b, htr058a, htr134a, htr235a, htr349a, htr4910a, htr5810a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc789xy, htr467b, htr479b, htr4910a, htr678a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd910b, htr035b, htr058a, htr235a, htr589a, htr8910a]
          ·
            linarith only [hlam, hd78a, hd89b, htr467b, htr479a, htr678a, htr7910a, htr8910a]

theorem shard_200 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr028a : m.d 2 8 + lam ≤ m.d 0 2)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr046a : m.d 0 4 + lam ≤ m.d 4 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr057a : m.d 0 5 + lam ≤ m.d 5 7)
    (htr057b : m.d 0 5 < m.d 0 7)
    (htr058a : m.d 0 5 + lam ≤ m.d 5 8)
    (htr058b : m.d 0 5 < m.d 0 8)
    (htr059a : m.d 0 5 + lam ≤ m.d 5 9)
    (htr059b : m.d 0 5 < m.d 0 9)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr146a : m.d 1 4 + lam ≤ m.d 4 6)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_200 m htr015a htr017c htr028a htr034b htr035b htr036a htr046a htr046b htr046c htr057a htr057b htr058a htr058b htr059a htr059b htr126a htr134a htr134b htr146a htr157a htr234a htr234c htr235a htr236c htr245a htr246b htr345a htr346a htr347a

#print axioms shard_200
end Jsp404.NoSatElevenDBMTerminal
