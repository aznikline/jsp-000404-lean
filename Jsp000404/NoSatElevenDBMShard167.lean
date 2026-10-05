import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_167 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr057a : m.d 5 7 + lam ≤ m.d 0 5)
    (htr057c : m.d 0 7 < m.d 0 5)
    (htr058a : m.d 5 8 + lam ≤ m.d 0 5)
    (htr058c : m.d 0 8 < m.d 0 5)
    (htr059a : m.d 5 9 + lam ≤ m.d 0 5)
    (htr059c : m.d 0 9 < m.d 0 5)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
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
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr034c, htr047a, htr347a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr046c, htr047b, htr067c])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, hc456yx, htr145a, htr147a, htr346a, htr347a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc456yx, htr046b, htr067a, htr145a, htr146c, htr167a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, htr234c, htr247a, htr347a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, htr046b, htr067a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hc678yx, htr034c, htr046a, htr347a, htr467c, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hc456yx, htr145a, htr146c, htr168a, htr468a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hc679yx, htr034c, htr046a, htr347a, htr467c, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  rcases m.htr 3 4 8 (by decide) (by decide) with
    ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
  ·
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, htr034c, htr048a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    rcases m.htr 3 4 9 (by decide) (by decide) with
      ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
    ·
      have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr049a, htr049b, htr049c, _, _⟩
        linarith only [hlam, htr034c, htr049a, htr349a])
      obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
      rcases m.htr 3 4 10 (by decide) (by decide) with
        ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
      ·
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
            linarith only [hlam, hd01a, hd89b, htr016a, htr167a, htr678a, htr789a])
          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hd23a, hd78b, htr234a, htr348a, htr489a, htr789a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
            linarith only [hlam, hc468xy, htr046a, htr048b, htr089a, htr489a])
          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hc013yz, hc578yz, htr035c, htr036a, htr058c, htr089a, htr135a, htr136b, htr167a, htr589a, htr678a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr479a, htr479b, htr479c, _, _⟩
            linarith only [hlam, hc123zy, hc789zy, htr035c, htr058a, htr135a, htr234a, htr347a, htr479a, htr589a])
          obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hc123zy, hc8910xy, htr035c, htr058a, htr135a, htr234a, htr348a, htr4810a, htr589a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
            linarith only [hlam, hc468xy, htr046a, htr048b, htr0810a, htr4810a])
          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
          have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
            linarith only [hlam, hc013yz, hc578yz, htr035c, htr036a, htr058c, htr0810a, htr135a, htr136b, htr167a, htr5810a, htr678a])
          obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
          have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
            linarith only [hlam, hc123zy, hc8910yz, htr035c, htr058a, htr135a, htr234a, htr349a, htr4910a, htr5810a])
          obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc789yx, htr467c, htr479c, htr4910a, htr678a, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hd78b, hd89a, htr467c, htr479a, htr678a, htr7910a, htr8910a]
          ·
            linarith only [hlam, hd13b, hd910a, htr035c, htr058a, htr135a, htr589a, htr8910a]
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr234a, htr347a, htr478a, htr678a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, hc467xy, htr046a, htr047b, htr078a, htr478a])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr278a, htr278b, htr278c, _, _⟩
            linarith only [hlam, hc467xy, htr246a, htr247b, htr278a, htr478a])
          obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
          rcases m.htr 5 7 8 (by decide) (by decide) with
            ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
          ·
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd13b, hd79a, htr035c, htr057c, htr078a, htr135a, htr578a, htr579a])
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
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc468xy, htr046a, htr048b, htr089a, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc123zy, hc8910yx, htr035c, htr057c, htr078a, htr135a, htr234a, htr348a, htr489a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                linarith only [hlam, hc567yz, htr468c, htr4810a, htr578a, htr678c, htr7810a])
              obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
              have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                linarith only [hlam, hc123zy, hc8910zy, htr035c, htr059a, htr135a, htr234a, htr348a, htr4810a, htr5910a])
              obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
              have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                linarith only [hlam, hc013yz, hc579yz, htr035c, htr036a, htr059c, htr0910a, htr135a, htr136b, htr167a, htr5910a, htr679a])
              obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
              ·
                linarith only [hlam, hd57a, hd89b, htr027b, htr079b, htr0910a, htr278a, htr578a, htr8910a]
            ·
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hc567yz, htr027b, htr079a, htr278a, htr578a, htr679a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
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
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc468xy, htr046a, htr048b, htr0810a, htr4810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc469xy, htr046a, htr049b, htr0910a, htr4910a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hc123zy, hc8910xy, htr035c, htr057c, htr078a, htr135a, htr234a, htr348a, htr4810a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc567yz, htr468c, htr489a, htr578a, htr678c, htr789a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                ·
                  linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
              ·
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc567yz, htr468c, htr489a, htr578a, htr678c, htr789a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910yx, htr035c, htr057c, htr078a, htr135a, htr234a, htr348a, htr489a, htr7810a])
                  obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc567yz, htr468c, htr4810a, htr578a, htr678c, htr7810a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910zy, htr035c, htr059a, htr135a, htr234a, htr348a, htr4810a, htr5910a])
                  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
                  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                    linarith only [hlam, hc123zy, hc589yz, htr035c, htr059c, htr0910a, htr135a, htr234a, htr348a, htr489a, htr5910a])
                  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc469xy, htr046a, htr049b, htr0910a, htr4910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd23a, hd910b, htr234a, htr348a, htr489a, htr8910a]
                  ·
                    linarith only [hlam, hd23a, hd89b, htr234a, htr349a, htr4910a, htr8910a]
                ·
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910xy, htr035c, htr057c, htr078a, htr135a, htr234a, htr348a, htr4810a, htr789a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                    linarith only [hlam, hc468xy, htr046a, htr048b, htr0810a, htr4810a])
                  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd13b, hd58a, htr035c, htr057c, htr078a, htr135a, htr589a, htr789a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                    linarith only [hlam, hd13b, hd89a, htr035c, htr058c, htr0810a, htr135a, htr5810a, htr589a])
                  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910yz, htr035c, htr058a, htr135a, htr234a, htr349a, htr4910a, htr5810a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hc567yz, htr469c, htr4910a, htr579a, htr679c, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd13b, hd89a, htr035c, htr057c, htr079a, htr135a, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hd13b, hd910a, htr035c, htr057c, htr078a, htr135a, htr789a, htr8910a]
          ·
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc123zy, hc789xy, htr035c, htr057a, htr135a, htr234a, htr347a, htr479a, htr578a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, hc467xy, htr046a, htr047b, htr079a, htr479a])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
              linarith only [hlam, hc123zy, hc7810xy, htr035c, htr057a, htr135a, htr234a, htr347a, htr4710a, htr578a])
            obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, hc467xy, htr046a, htr047b, htr0710a, htr4710a])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd13b, hd78a, htr035c, htr057c, htr079a, htr135a, htr578a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hc123zy, hc789yz, htr035c, htr057a, htr135a, htr234a, htr348a, htr489a, htr579a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
              linarith only [hlam, hc468xy, htr046a, htr048b, htr089a, htr489a])
            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
            have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
              linarith only [hlam, hd13b, hd78a, htr035c, htr057c, htr0710a, htr135a, htr5710a, htr578a])
            obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
              linarith only [hlam, hc123zy, hc7910yz, htr035c, htr057a, htr135a, htr234a, htr349a, htr4910a, htr5710a])
            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hd13b, hd89a, htr035c, htr057a, htr135a, htr578a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              linarith only [hlam, hd13b, hd910a, htr035c, htr057a, htr135a, htr579a, htr7910a])
            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hc478zy, htr489c, htr4910a, htr789a, htr8910a]
            ·
              linarith only [hlam, hd13b, hd79a, htr035c, htr058c, htr089a, htr135a, htr7910a, htr8910a]
      ·
        have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
          linarith only [hlam, hc456yx, htr0410a, htr046a, htr3410a, htr345a])
        obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
        have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
          linarith only [hlam, htr0410c, htr047b, htr0710b])
        obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
          linarith only [hlam, htr0410c, htr048b, htr0810b])
        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
        have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
          linarith only [hlam, hc123zy, htr035c, htr057c, htr0710a, htr135a, htr234a, htr347a, htr4710a])
        obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc7810yx, htr134b, htr147a, htr3410a, htr4710b, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc467xy, htr046a, htr047b, htr078a, htr478a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
          linarith only [hlam, hc123zy, htr035c, htr058c, htr0810a, htr135a, htr234a, htr348a, htr4810a])
        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
        have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
          linarith only [hlam, hc457zy, htr3410a, htr347a, htr4710b, htr5710a])
        obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd13b, hd710a, htr035c, htr057c, htr078a, htr135a, htr5710a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc478zy, htr3410a, htr348a, htr4810b, htr7810a]
        ·
          linarith only [hlam, hd13b, hd810a, htr035c, htr057a, htr135a, htr578a, htr7810a]
    ·
      have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr049a, htr049b, htr049c, _, _⟩
        linarith only [hlam, hc456yx, htr046a, htr049a, htr345a, htr349a])
      obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, htr047b, htr049c, htr079b])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
        linarith only [hlam, htr048b, htr049c, htr089b])
      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc123zy, htr035c, htr057c, htr079a, htr135a, htr234a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc789yx, htr134b, htr147a, htr349a, htr478a, htr479b])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc467xy, htr046a, htr047b, htr078a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc123zy, htr035c, htr058c, htr089a, htr135a, htr234a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc457zy, htr347a, htr349a, htr479b, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd13b, hd79a, htr035c, htr057c, htr078a, htr135a, htr578a, htr579a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc478zy, htr348a, htr349a, htr489b, htr789a]
      ·
        linarith only [hlam, hd13b, hd89a, htr035c, htr057a, htr135a, htr578a, htr789a]
  ·
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc456yx, htr046a, htr048a, htr345a, htr348a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, htr047b, htr048c, htr078b])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr148a, htr148b, htr148c, _, _⟩
      linarith only [hlam, htr134b, htr148a, htr348a])
    obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hc123zy, htr035c, htr057c, htr078a, htr135a, htr234a, htr347a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hc789xy, htr134b, htr147a, htr348a, htr478b, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
      linarith only [hlam, hc467xy, htr046a, htr047b, htr079a, htr479a])
    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc457zy, htr347a, htr348a, htr478b, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd13b, hd78a, htr035c, htr057c, htr079a, htr135a, htr578a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hc013yz, hc789yz, htr035c, htr036a, htr057a, htr135a, htr136b, htr168a, htr579a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hc012xy, hc678zy, htr018a, htr025a, htr189a, htr257a, htr578a, htr689a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc458yx, htr145a, htr148c, htr189a, htr489a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd13b, hd78a, htr134a, htr348a, htr489a, htr789a]
    ·
      linarith only [hlam, hd13b, hd89a, htr035c, htr057a, htr135a, htr578a, htr789a]

theorem shard_167 {lam p : ℝ} (m : ElevenModel lam p)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr027b : m.d 2 7 < m.d 0 7)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036a : m.d 0 3 + lam ≤ m.d 3 6)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr057a : m.d 5 7 + lam ≤ m.d 0 5)
    (htr057c : m.d 0 7 < m.d 0 5)
    (htr058a : m.d 5 8 + lam ≤ m.d 0 5)
    (htr058c : m.d 0 8 < m.d 0 5)
    (htr059a : m.d 5 9 + lam ≤ m.d 0 5)
    (htr059c : m.d 0 9 < m.d 0 5)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr257a : m.d 5 7 + lam ≤ m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    : False :=
  proof_shard_167 m htr016a htr018a htr025a htr027b htr034c htr035c htr036a htr046a htr046b htr046c htr057a htr057c htr058a htr058c htr059a htr059c htr134a htr134b htr135a htr136b htr145a htr146c htr234a htr234c htr246a htr257a htr345a htr346a htr347a

#print axioms shard_167
end Jsp404.NoSatElevenDBMTerminal
