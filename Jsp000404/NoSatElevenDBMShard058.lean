import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_058 {lam p : ℝ} (m : ElevenModel lam p)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr028c : m.d 0 8 < m.d 2 8)
    (htr029c : m.d 0 9 < m.d 2 9)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr037b : m.d 3 7 < m.d 0 7)
    (htr038b : m.d 3 8 < m.d 0 8)
    (htr039b : m.d 3 9 < m.d 0 9)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  have hd02a := (m.hrange 0 2 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  have hd69a := (m.hrange 6 9 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hd23b, hd34a, htr123a, htr124a, htr245a, htr345a])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr123a, htr124a, htr245a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd23b, hd45a, htr123a, htr125a, htr256a, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd23b, hd57a, htr123a, htr124a, htr245a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hd23b, hd45a, htr123a, htr125a, htr257a, htr457a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hd23b, hd45a, htr024c, htr046a, htr123a, htr124a, htr345a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr146a, htr146b, htr146c, _, _⟩
      linarith only [hlam, hd23b, hd45a, htr123a, htr124c, htr146a, htr345a, htr346a])
    obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd23b, hd45a, htr024c, htr047a, htr123a, htr124a, htr345a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        rcases m.htr 3 4 9 (by decide) (by decide) with
          ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
        ·
          rcases m.htr 3 4 10 (by decide) (by decide) with
            ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
          ·
            rcases m.htr 3 6 7 (by decide) (by decide) with
              ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
            ·
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd45a, hd78b, htr345a, htr346a, htr467a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hc457xy, htr037b, htr078a, htr345a, htr347b, htr478a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd45a, hd79b, htr345a, htr346a, htr467a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr479a, htr679a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hc457xy, htr037b, htr079a, htr345a, htr347b, htr479a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd23b, hd89a, htr027c, htr078a, htr123a, htr127a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, hd23b, hd78a, htr028c, htr089a, htr123a, htr128a, htr789a])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hc458xy, htr038b, htr089a, htr345a, htr348b, htr489a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd23b, hd910a, htr027c, htr079a, htr123a, htr127a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                linarith only [hlam, hd23b, hd79a, htr029c, htr0910a, htr123a, htr129a, htr7910a])
              obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc459xy, htr039b, htr0910a, htr345a, htr349b, htr4910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd45a, hd910b, htr345a, htr348a, htr489a, htr8910a]
              ·
                linarith only [hlam, hd45a, hd89b, htr345a, htr349a, htr4910a, htr8910a]
            ·
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd23b, hd78a, htr123a, htr126a, htr236b, htr367a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                linarith only [hlam, hd23b, hd67a, htr027c, htr078a, htr123a, htr127a, htr678a])
              obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc457xy, htr037b, htr078a, htr345a, htr347b, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd23b, hd79a, htr123a, htr126a, htr236b, htr367a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, hd23b, hd67a, htr027c, htr079a, htr123a, htr127a, htr679a])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc457xy, htr037b, htr079a, htr345a, htr347b, htr479a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hd45a, hd89b, htr345a, htr347a, htr478a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, hd45a, hd78b, htr345a, htr348a, htr489a, htr789a])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, hc458xy, htr038b, htr089a, htr345a, htr348b, htr489a])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd45a, hd910b, htr345a, htr347a, htr479a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hd45a, hd79b, htr345a, htr349a, htr4910a, htr7910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                linarith only [hlam, hc459xy, htr039b, htr0910a, htr345a, htr349b, htr4910a])
              obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd23b, hd89a, htr029c, htr0910a, htr123a, htr129a, htr8910a]
              ·
                linarith only [hlam, hd23b, hd910a, htr028c, htr089a, htr123a, htr128a, htr8910a]
          ·
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, htr034b, htr0410a, htr3410a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
              linarith only [hlam, htr0410c, htr046b, htr0610b])
            obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0410c, htr047b, htr0710b])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, hd23b, hd45a, htr026c, htr0610a, htr123a, htr126a, htr345a, htr346a, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc6710yx, htr034b, htr046a, htr3410a, htr4610b, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hc456xy, htr036b, htr067a, htr345a, htr346b, htr467a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            rcases m.htr 6 7 10 (by decide) (by decide) with
              ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            ·
              linarith only [hlam, hd23b, hd67a, htr027c, htr0710a, htr123a, htr127a, htr6710a]
            ·
              linarith only [hlam, hd23b, hd710a, htr026c, htr067a, htr123a, htr126a, htr6710a]
        ·
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, htr034b, htr049a, htr349a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr069a, htr069b, htr069c, _, _⟩
            linarith only [hlam, htr046b, htr049c, htr069b])
          obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr047b, htr049c, htr079b])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hd23b, hd45a, htr026c, htr069a, htr123a, htr126a, htr345a, htr346a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc679yx, htr034b, htr046a, htr349a, htr467a, htr469b])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr067a, htr067b, htr067c, _, _⟩
            linarith only [hlam, hc456xy, htr036b, htr067a, htr345a, htr346b, htr467a])
          obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
          rcases m.htr 6 7 9 (by decide) (by decide) with
            ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
          ·
            linarith only [hlam, hd23b, hd67a, htr027c, htr079a, htr123a, htr127a, htr679a]
          ·
            linarith only [hlam, hd23b, hd79a, htr026c, htr067a, htr123a, htr126a, htr679a]
      ·
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, htr034b, htr048a, htr348a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr046b, htr048c, htr068b])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr047b, htr048c, htr078b])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hd23b, hd45a, htr026c, htr068a, htr123a, htr126a, htr345a, htr346a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc678yx, htr034b, htr046a, htr348a, htr467a, htr468b])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc456xy, htr036b, htr067a, htr345a, htr346b, htr467a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          linarith only [hlam, hd23b, hd67a, htr027c, htr078a, htr123a, htr127a, htr678a]
        ·
          linarith only [hlam, hd23b, hd78a, htr026c, htr067a, htr123a, htr126a, htr678a]
    ·
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
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, hd23b, hd45a, htr026c, htr067a, htr123a, htr126a, htr345a, htr346a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc678xy, htr034b, htr046a, htr347a, htr467b, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc456xy, htr036b, htr068a, htr345a, htr346b, htr468a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc679xy, htr034b, htr046a, htr347a, htr467b, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr069a, htr069b, htr069c, _, _⟩
        linarith only [hlam, hc456xy, htr036b, htr069a, htr345a, htr346b, htr469a])
      obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr123a, htr124a, htr234b, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc467yx, htr146a, htr147c, htr178a, htr478a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd23b, hd79a, htr123a, htr124a, htr234b, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc467yx, htr146a, htr147c, htr179a, htr479a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, htr467b, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, htr467b, htr479a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd23b, hd89a, htr026c, htr068a, htr123a, htr126a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hd23b, hd68a, htr123a, htr128a, htr289a, htr689a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd23b, hd910a, htr026c, htr069a, htr123a, htr126a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd02a, hd89b, htr025a, htr257a, htr578a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd01a, hd79b, htr017a, htr178a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc567zy, htr579a, htr679b, htr6910a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd01a, hd910b, htr017a, htr178a, htr789a, htr8910a]
        ·
          linarith only [hlam, hd01a, hd89b, htr017a, htr179a, htr7910a, htr8910a]
      ·
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd01a, hd78b, htr017a, htr179a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd02a, hd910b, htr025a, htr257a, htr579a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd02a, hd79b, htr028a, htr289a, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd23b, hd67a, htr123a, htr124a, htr234b, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd23b, hd46a, htr123a, htr126a, htr267a, htr467a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd23b, hd68a, htr123a, htr124a, htr234b, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd23b, hd46a, htr123a, htr126a, htr268a, htr468a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
      linarith only [hlam, hd23b, hd69a, htr123a, htr124a, htr234b, htr346a, htr469a])
    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
    have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr269a, htr269b, htr269c, _, _⟩
      linarith only [hlam, hd23b, hd46a, htr123a, htr126a, htr269a, htr469a])
    obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hd02a, hd67b, htr026a, htr268a, htr567a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hd02a, hd67b, htr026a, htr269a, htr567a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd02a, hd78b, htr025a, htr256a, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd02a, hd79b, htr025a, htr256a, htr567a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd02a, hd89b, htr025a, htr256a, htr568a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd02a, hd910b, htr025a, htr256a, htr569a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 3 4 7 (by decide) (by decide) with
        ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
      ·
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr478a, htr678a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, hc457xy, htr037b, htr078a, htr345a, htr347b, htr478a])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr345a, htr347a, htr479a, htr679a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, hc457xy, htr037b, htr079a, htr345a, htr347b, htr479a])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd23b, hd89a, htr027c, htr078a, htr123a, htr127a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd23b, hd910a, htr027c, htr079a, htr123a, htr127a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
      ·
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd23b, hd78a, htr123a, htr124a, htr234b, htr347a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc467yz, htr034b, htr048a, htr347a, htr478c, htr678a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd23b, hd89a, htr024c, htr048a, htr123a, htr124a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a]
        ·
          linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc456yz, htr034b, htr047a, htr346a, htr467c, htr567a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd23b, hd78a, htr024c, htr047a, htr123a, htr124a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hd02a, hd68b, htr026a, htr267a, htr567a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc456yz, htr034b, htr048a, htr346a, htr468c, htr568a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd23b, hd89a, htr024c, htr048a, htr123a, htr124a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc456yz, htr468b, htr489a, htr568a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd02a, hd89b, htr026a, htr267a, htr678a, htr789a]
      ·
        linarith only [hlam, hd02a, hd78b, htr026a, htr268a, htr689a, htr789a]

theorem shard_058 {lam p : ℝ} (m : ElevenModel lam p)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025a : m.d 0 2 + lam ≤ m.d 2 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr027c : m.d 0 7 < m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr028c : m.d 0 8 < m.d 2 8)
    (htr029c : m.d 0 9 < m.d 2 9)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr036b : m.d 3 6 < m.d 0 6)
    (htr037b : m.d 3 7 < m.d 0 7)
    (htr038b : m.d 3 8 < m.d 0 8)
    (htr039b : m.d 3 9 < m.d 0 9)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr124c : m.d 1 4 < m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    : False :=
  proof_shard_058 m htr017a htr024c htr025a htr026a htr026c htr027c htr028a htr028c htr029c htr034b htr036b htr037b htr038b htr039b htr123a htr124a htr124c htr125a htr126a htr127a htr128a htr129a htr134b htr234b htr236b htr245a

#print axioms shard_058
end Jsp404.NoSatElevenDBMTerminal
