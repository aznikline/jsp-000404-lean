import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_176 {lam p : ℝ} (m : ElevenModel lam p)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr048c : m.d 0 8 < m.d 0 4)
    (htr049c : m.d 0 9 < m.d 0 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr138b : m.d 3 8 < m.d 1 8)
    (htr139b : m.d 3 9 < m.d 1 9)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr239a : m.d 2 3 + lam ≤ m.d 3 9)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr348c : m.d 3 8 < m.d 3 4)
    (htr349a : m.d 4 9 + lam ≤ m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd59a := (m.hrange 5 9 (by decide)).1
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
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc479xy, hc479yx, hc479yz, hc479zy⟩ := endpoint_caps m 4 7 9 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc123zy, htr025b, htr056a, htr134a, htr235b, htr345c, htr356a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr135b, htr156a, htr356a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd13b, hd57a, htr134a, htr345c, htr356a, htr456a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd13b, hd58a, htr134a, htr345c, htr356a, htr456a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hd13b, hd59a, htr134a, htr345c, htr356a, htr456a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  rcases m.htr 3 5 7 (by decide) (by decide) with
    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr035c, htr057a, htr357a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr056c, htr057b, htr067c])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, htr056b, htr067a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hc678yx, htr035c, htr056a, htr357a, htr567c, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hc145zy, htr156c, htr168a, htr456a, htr568a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
      linarith only [hlam, hc679yx, htr035c, htr056a, htr357a, htr567c, htr569a])
    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
      linarith only [hlam, hc145zy, htr156c, htr169a, htr456a, htr569a])
    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd45a, hd78b, htr356a, htr357a, htr456a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc567xy, htr056a, htr057b, htr078a, htr578a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd45a, hd79b, htr356a, htr357a, htr456a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
      linarith only [hlam, hc567xy, htr056a, htr057b, htr079a, htr579a])
    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
      linarith only [hlam, hd45a, hd710b, htr356a, htr357a, htr456a, htr5710a])
    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
    have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
      linarith only [hlam, hc567xy, htr056a, htr057b, htr0710a, htr5710a])
    obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
    rcases m.htr 4 7 8 (by decide) (by decide) with
      ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc457yz, htr035c, htr058a, htr357a, htr478a, htr578b])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd13b, hd79a, htr034c, htr047c, htr078a, htr134a, htr478a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
        linarith only [hlam, hc457yz, htr035c, htr059a, htr357a, htr479a, htr579b])
      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd45a, hd89b, htr056a, htr058a, htr456a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
        linarith only [hlam, hd45a, hd910b, htr056a, htr059a, htr456a, htr5910a])
      obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, hc457yz, htr478a, htr578c, htr589a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hc457yz, htr479a, htr579c, htr5910a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        linarith only [hlam, hd13b, hd89a, htr034c, htr047c, htr079a, htr134a, htr7910a, htr8910a]
      ·
        linarith only [hlam, hd13b, hd910a, htr034c, htr047c, htr078a, htr134a, htr789a, htr8910a]
    ·
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr034c, htr047c, htr079a, htr134a, htr478a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hd13b, hd78a, htr034c, htr047c, htr0710a, htr134a, htr4710a, htr478a])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hc123zy, hc789yz, htr134a, htr136b, htr168a, htr236a, htr347a, htr479a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc123zy, hc678zy, htr134a, htr238a, htr347a, htr389a, htr478a, htr689a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hc123zy, hc7910yz, htr134a, htr136b, htr169a, htr236a, htr347a, htr4710a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
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
        linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
      ·
        linarith only [hlam, hd13b, hd79a, htr134a, htr348c, htr389a, htr7910a, htr8910a]
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hc345zy, htr056a, htr057a, htr357a, htr456a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr135b, htr157a, htr357a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    rcases m.htr 3 5 8 (by decide) (by decide) with
      ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr035c, htr058a, htr358a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, htr056c, htr058b, htr068c])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr057c, htr058b, htr078c])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, htr056b, htr068a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc678xy, htr035c, htr056a, htr358a, htr567a, htr568c])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc145zy, htr156c, htr167a, htr456a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, htr057b, htr078a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc789yx, htr035c, htr057a, htr358a, htr578c, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd45a, hd89b, htr356a, htr358a, htr456a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
        linarith only [hlam, hc568xy, htr056a, htr058b, htr089a, htr589a])
      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr356a, htr358a, htr456a, htr578c, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc123zy, hc478yz, htr034c, htr048c, htr089a, htr134a, htr136b, htr167a, htr236a, htr489a, htr678a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        linarith only [hlam, hc123zy, hc789zy, htr134a, htr136b, htr167a, htr236a, htr348a, htr489a, htr679a]
      ·
        linarith only [hlam, hd45a, hd78b, htr457a, htr579a, htr678a, htr679a]
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc345zy, htr056a, htr058a, htr358a, htr456a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr135b, htr158a, htr358a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      rcases m.htr 3 5 9 (by decide) (by decide) with
        ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
      ·
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, htr035c, htr059a, htr359a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, htr056c, htr059b, htr069c])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr057c, htr059b, htr079c])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, htr056b, htr069a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hc679xy, htr035c, htr056a, htr359a, htr567a, htr569c])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc145zy, htr156c, htr167a, htr456a, htr567a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, htr057b, htr079a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
          linarith only [hlam, hc7910yx, htr035c, htr057a, htr359a, htr5710a, htr579c])
        obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd45a, hd910b, htr356a, htr359a, htr456a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
          linarith only [hlam, hc569xy, htr056a, htr059b, htr0910a, htr5910a])
        obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd45a, hd67b, htr356a, htr359a, htr456a, htr579c, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hc123zy, hc479yz, htr034c, htr049c, htr0910a, htr134a, htr136b, htr167a, htr236a, htr4910a, htr679a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        rcases m.htr 6 7 10 (by decide) (by decide) with
          ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
        ·
          linarith only [hlam, hc123zy, hc7910zy, htr134a, htr136b, htr167a, htr236a, htr349a, htr4910a, htr6710a]
        ·
          linarith only [hlam, hd45a, hd79b, htr457a, htr5710a, htr6710a, htr679a]
      ·
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, htr135b, htr159a, htr359a])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        rcases m.htr 3 5 10 (by decide) (by decide) with
          ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
        ·
          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
            linarith only [hlam, htr035c, htr0510a, htr3510a])
          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
            linarith only [hlam, htr0510b, htr056c, htr0610c])
          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0510b, htr057c, htr0710c])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
            linarith only [hlam, htr0510b, htr058c, htr0810c])
          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
          have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
            linarith only [hlam, htr056b, htr0610a, htr5610a])
          obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc6710xy, htr035c, htr056a, htr3510a, htr5610c, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, htr057b, htr0710a, htr5710a])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc7810xy, htr035c, htr057a, htr3510a, htr5710c, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
            linarith only [hlam, htr058b, htr0810a, htr5810a])
          obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hd45a, hd67b, htr3510a, htr356a, htr456a, htr5710c, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd45a, hd710b, htr457a, htr578a, htr6710a, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd45a, hd810b, htr456a, htr567a, htr678a, htr7810a]
          ·
            linarith only [hlam, hd45a, hd78b, htr3510a, htr356a, htr456a, htr5810c, htr7810a]
        ·
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr067a, htr067b, htr067c, _, _⟩
              linarith only [hlam, hd13b, hd45a, htr034c, htr046c, htr067a, htr134a, htr456a, htr567a])
            obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc145zy, htr156c, htr167a, htr456a, htr567a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, htr456c, htr467a, htr567a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc145zy, htr156c, htr168a, htr456a, htr568a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              rcases m.htr 5 7 8 (by decide) (by decide) with
                ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, hd13b, hd45a, htr034c, htr047c, htr078a, htr134a, htr457a, htr578a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc145zy, htr157c, htr178a, htr457a, htr578a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, htr457c, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc123zy, hc789yx, htr134a, htr136b, htr167a, htr236a, htr345c, htr357a, htr579a, htr678a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, hc123zy, hc7810yx, htr134a, htr136b, htr167a, htr236a, htr345c, htr357a, htr5710a, htr678a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd45a, hd78b, htr457a, htr579a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc123zy, hc789zy, htr134a, htr136b, htr167a, htr236a, htr348a, htr489a, htr679a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                    linarith only [hlam, hc123zy, hc478yz, htr034c, htr048c, htr089a, htr134a, htr136b, htr167a, htr236a, htr489a, htr678a])
                  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd45a, hd78b, htr457a, htr5710a, htr6710a, htr678a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hc123zy, hc7910zy, htr134a, htr136b, htr167a, htr236a, htr349a, htr4910a, htr6710a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                    linarith only [hlam, hd45a, hd89b, htr456a, htr567a, htr678a, htr789a])
                  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                    linarith only [hlam, hd45a, hd910b, htr456a, htr567a, htr679a, htr7910a])
                  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd45a, hd79b, htr058b, htr089a, htr458a, htr7910a, htr8910a]
                  ·
                    linarith only [hlam, hc478yz, htr489b, htr4910a, htr789a, htr8910a]
                ·
                  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                    linarith only [hlam, hc679yx, htr067b, htr069a, htr078a, htr678a])
                  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                    linarith only [hlam, hd45a, hd67b, htr056b, htr069a, htr167b, htr169a, htr178a, htr456a, htr678a])
                  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hd45a, hd79b, htr457a, htr578a, htr678a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  rcases m.htr 5 7 9 (by decide) (by decide) with
                    ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                  ·
                    have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                      linarith only [hlam, hc567yz, htr017c, htr079a, htr178a, htr579a, htr678a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                      linarith only [hlam, hc567yz, htr178a, htr179a, htr579a, htr678a])
                    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                      linarith only [hlam, htr457c, htr479a, htr579a])
                    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                    rcases m.htr 5 7 10 (by decide) (by decide) with
                      ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    ·
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                          linarith only [hlam, hc123zy, hc8910yx, htr134a, htr137b, htr178a, htr237a, htr348a, htr4810a, htr789a])
                        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                        have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                          linarith only [hlam, hc467yz, htr078c, htr0810a, htr478b, htr4810a, htr678a])
                        obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hd45a, hd68b, htr457a, htr578a, htr689a, htr789a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                          linarith only [hlam, hd45a, hd89b, htr058b, htr0810a, htr458a, htr6810a, htr689a])
                        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                          linarith only [hlam, hc123zy, hc8910zy, htr134a, htr136b, htr168a, htr236a, htr349a, htr4910a, htr6810a])
                        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                          linarith only [hlam, hc467yz, htr479b, htr4910a, htr679a, htr7910a])
                        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd45a, hd910b, htr457a, htr578a, htr789a, htr8910a]
                        ·
                          linarith only [hlam, hd45a, hd89b, htr457a, htr579a, htr7910a, htr8910a]
                      ·
                        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                          linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a])
                        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc123zy, hc8910xy, htr134a, htr137b, htr178a, htr237a, htr348a, htr489a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                          linarith only [hlam, hc467yz, htr478b, htr4810a, htr678a, htr7810a])
                        obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hc123zy, hc8910yz, htr134a, htr136b, htr169a, htr236a, htr348a, htr4810a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                          linarith only [hlam, hc012xy, hc689zy, htr019a, htr024a, htr1910a, htr248a, htr489a, htr6910a])
                        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                          linarith only [hlam, hc467yz, htr179c, htr1910a, htr479b, htr4910a, htr679a])
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
                        linarith only [hlam, htr057b, htr0710a, htr5710a])
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
                        linarith only [hlam, hc467yz, htr078c, htr0810a, htr478b, htr4810a, htr678a])
                      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                      have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                        linarith only [hlam, hc123zy, hc467yz, htr034c, htr049c, htr0910a, htr134a, htr137b, htr178a, htr237a, htr479b, htr4910a, htr678a])
                      obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hc123zy, hc8910yx, htr134a, htr137b, htr178a, htr237a, htr348a, htr4810a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                        linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a])
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
                      linarith only [hlam, htr057b, htr079a, htr579a])
                    obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                    have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                      linarith only [hlam, htr078b, htr079c, htr089b])
                    obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                      linarith only [hlam, hc123zy, htr134a, htr137b, htr179a, htr237a, htr345c, htr357a, htr579a])
                    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hc467yz, htr078c, htr089a, htr478b, htr489a, htr678a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910xy, htr134a, htr137b, htr178a, htr237a, htr348a, htr489a, htr7810a])
                    obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                    have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                      linarith only [hlam, hc467yz, htr478b, htr4810a, htr678a, htr7810a])
                    obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910yz, htr134a, htr136b, htr169a, htr236a, htr348a, htr4810a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                      linarith only [hlam, hc123zy, hc679zy, htr134a, htr139b, htr1910a, htr239a, htr345c, htr357a, htr579a, htr6910a])
                    obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd67b, hd89a, htr178a, htr179c, htr1910a, htr678a, htr8910a]
                    ·
                      linarith only [hlam, hd13b, hd910a, htr134a, htr348a, htr489a, htr8910a]
              ·
                have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                  linarith only [hlam, htr057b, htr078a, htr578a])
                obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd13b, hd47a, htr134a, htr345c, htr357a, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                  linarith only [hlam, hd13b, hd89a, htr134a, htr345c, htr357a, htr578a, htr789a])
                obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd13b, hd78a, htr134a, htr345c, htr358a, htr589a, htr789a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc145zy, htr158c, htr189a, htr458a, htr589a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc123zy, hc678zy, htr134a, htr138b, htr189a, htr238a, htr345c, htr357a, htr578a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc123zy, hc789yz, htr134a, htr136b, htr168a, htr236a, htr347a, htr479a, htr689a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                  linarith only [hlam, hd13b, hd78a, htr034c, htr047c, htr079a, htr134a, htr478a, htr479a])
                obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc123zy, hc8910yx, htr134a, htr136b, htr168a, htr236a, htr348a, htr4810a, htr689a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, hc789xy, htr078c, htr079a, htr0810a, htr478b, htr4810a])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hd45a, hd89b, htr058b, htr0810a, htr458a, htr6810a, htr689a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                  linarith only [hlam, hc123zy, hc8910zy, htr134a, htr136b, htr168a, htr236a, htr349a, htr4910a, htr6810a])
                obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                  linarith only [hlam, hc789xy, htr478a, htr479b, htr4910a, htr7910a])
                obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd45a, hd910b, htr456a, htr568a, htr689a, htr8910a]
                ·
                  linarith only [hlam, hd78a, hd89b, htr478a, htr479a, htr7910a, htr8910a]
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
                linarith only [hlam, hc123zy, htr134a, htr136b, htr168a, htr236a, htr345c, htr356a, htr568a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, hd13b, hd46a, htr134a, htr345c, htr356a, htr468a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hd13b, hd68a, htr034c, htr047c, htr078a, htr134a, htr467b, htr468a, htr478a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc123zy, hc789xy, htr134a, htr136b, htr167a, htr236a, htr347a, htr478a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc678yx, htr467b, htr468a, htr479a, htr679a])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                linarith only [hlam, hc123zy, hc7810xy, htr134a, htr136b, htr167a, htr236a, htr347a, htr478a, htr6710a])
              obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
              have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                linarith only [hlam, hc678yx, htr467b, htr468a, htr4710a, htr6710a])
              obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd13b, hd89a, htr134a, htr345c, htr356a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc678yx, htr167a, htr168c, htr189a, htr689a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hd13b, hd910a, htr134a, htr347a, htr479a, htr7910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
                linarith only [hlam, hd13b, hd79a, htr134a, htr345c, htr359a, htr5910a, htr7910a])
              obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
              have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                linarith only [hlam, hc145zy, htr159c, htr1910a, htr459a, htr5910a])
              obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hc012xy, hc7910yz, htr018a, htr024a, htr189a, htr247a, htr4710a, htr8910a]
              ·
                linarith only [hlam, hc012xy, hc789yz, htr019a, htr024a, htr1910a, htr247a, htr479a, htr8910a]
          ·
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd13b, hd46a, htr134a, htr345c, htr356a, htr467a, htr567a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
              linarith only [hlam, hd13b, hd78a, htr134a, htr345c, htr356a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hd13b, hd67a, htr134a, htr345c, htr357a, htr578a, htr678a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc145zy, htr157c, htr178a, htr457a, htr578a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr679a, htr679b, htr679c, _, _⟩
              linarith only [hlam, hd13b, hd79a, htr134a, htr345c, htr356a, htr567a, htr679a])
            obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hd13b, hd67a, htr134a, htr345c, htr357a, htr579a, htr679a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc145zy, htr157c, htr179a, htr457a, htr579a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            rcases m.htr 5 6 8 (by decide) (by decide) with
              ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
            ·
              have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                linarith only [hlam, hd13b, hd45a, htr034c, htr046c, htr068a, htr134a, htr456a, htr568a])
              obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
              have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                linarith only [hlam, hc145zy, htr156c, htr168a, htr456a, htr568a])
              obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
              have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                linarith only [hlam, htr456c, htr468a, htr568a])
              obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
              rcases m.htr 5 6 9 (by decide) (by decide) with
                ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, hc678xy, htr068a, htr069a, htr567a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                  linarith only [hlam, hc678xy, htr168a, htr169a, htr567a, htr569a])
                obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                  linarith only [hlam, htr456c, htr469a, htr569a])
                obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                rcases m.htr 5 6 10 (by decide) (by decide) with
                  ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                ·
                  rcases m.htr 5 8 9 (by decide) (by decide) with
                    ⟨htr589a, htr589b, htr589c, _, _⟩ | ⟨htr589a, htr589b, htr589c, _, _⟩
                  ·
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hc678xy, htr567a, htr568b, htr589a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910yx, htr134a, htr136b, htr168a, htr236a, htr348a, htr4810a, htr689a])
                    obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc678xy, htr467a, htr468b, htr4810a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910zy, htr134a, htr136b, htr168a, htr236a, htr349a, htr4910a, htr6810a])
                    obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc679xy, htr467a, htr469b, htr4910a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd45a, hd910b, htr456a, htr568a, htr689a, htr8910a]
                    ·
                      linarith only [hlam, hd45a, hd89b, htr456a, htr569a, htr6910a, htr8910a]
                  ·
                    have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910xy, htr134a, htr136b, htr168a, htr236a, htr345c, htr358a, htr589a, htr6810a])
                    obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                    have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                      linarith only [hlam, hc678xy, htr467a, htr468b, htr4810a, htr6810a])
                    obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                    have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                      linarith only [hlam, hc123zy, hc8910yz, htr134a, htr136b, htr169a, htr236a, htr348a, htr4810a, htr6910a])
                    obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                    have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                      linarith only [hlam, hc679xy, htr467a, htr469b, htr4910a, htr6910a])
                    obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hd13b, hd89a, htr134a, htr349a, htr4910a, htr8910a]
                    ·
                      linarith only [hlam, hd13b, hd910a, htr134a, htr345c, htr358a, htr589a, htr8910a]
                ·
                  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                    linarith only [hlam, htr056b, htr0610a, htr5610a])
                  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                  have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                    linarith only [hlam, htr0610c, htr068b, htr0810b])
                  obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                  have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                    linarith only [hlam, htr0610c, htr069b, htr0910b])
                  obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, hd13b, hd67a, htr034c, htr048c, htr0810a, htr134a, htr467a, htr468b, htr4810a])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                    linarith only [hlam, hd13b, hd67a, htr034c, htr049c, htr0910a, htr134a, htr467a, htr469b, htr4910a])
                  obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc123zy, hc8910yx, htr134a, htr136b, htr168a, htr236a, htr348a, htr4810a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc678xy, htr467a, htr468b, htr489a, htr689a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd13b, hd89a, htr134a, htr349a, htr4910a, htr8910a]
                  ·
                    linarith only [hlam, hd13b, hd910a, htr134a, htr348a, htr489a, htr8910a]
              ·
                have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                  linarith only [hlam, htr056b, htr069a, htr569a])
                obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                  linarith only [hlam, htr068b, htr069c, htr089b])
                obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                  linarith only [hlam, hc123zy, htr134a, htr136b, htr169a, htr236a, htr345c, htr356a, htr569a])
                obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hd13b, hd67a, htr034c, htr048c, htr089a, htr134a, htr467a, htr468b, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                  linarith only [hlam, hc123zy, hc8910xy, htr134a, htr136b, htr168a, htr236a, htr348a, htr489a, htr6810a])
                obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                  linarith only [hlam, hc678xy, htr467a, htr468b, htr4810a, htr6810a])
                obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                  linarith only [hlam, hd13b, hd910a, htr134a, htr345c, htr356a, htr569a, htr6910a])
                obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                  linarith only [hlam, hc689yx, htr168a, htr169c, htr1910a, htr6910a])
                obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                rcases m.htr 7 9 10 (by decide) (by decide) with
                  ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                ·
                  linarith only [hlam, hc123zy, hc8910yz, htr134a, htr137b, htr179a, htr237a, htr348a, htr4810a, htr7910a]
                ·
                  linarith only [hlam, hc123zy, hc679yz, htr134a, htr139b, htr1910a, htr239a, htr345c, htr356a, htr569a, htr7910a]
            ·
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hd13b, hd89a, htr134a, htr345c, htr356a, htr568a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hd13b, hd68a, htr134a, htr345c, htr358a, htr589a, htr689a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc145zy, htr158c, htr189a, htr458a, htr589a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hd13b, hd810a, htr134a, htr345c, htr356a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                linarith only [hlam, hd13b, hd68a, htr134a, htr345c, htr358a, htr5810a, htr6810a])
              obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc145zy, htr158c, htr1810a, htr458a, htr5810a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                linarith only [hlam, hc123zy, hc678yz, htr134a, htr138b, htr189a, htr238a, htr345c, htr356a, htr568a, htr789a])
              obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, hc012xy, hc689yz, htr017a, htr024a, htr178a, htr246a, htr469a, htr789a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                linarith only [hlam, hc123zy, hc678yz, htr134a, htr138b, htr1810a, htr238a, htr345c, htr356a, htr568a, htr7810a])
              obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc123zy, hc8910zy, htr134a, htr137b, htr178a, htr237a, htr349a, htr4910a, htr7810a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hc679xy, htr467a, htr469b, htr4910a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              rcases m.htr 8 9 10 (by decide) (by decide) with
                ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
              ·
                linarith only [hlam, hd45a, hd910b, htr457a, htr578a, htr789a, htr8910a]
              ·
                linarith only [hlam, hd67a, hd89b, htr467a, htr469a, htr6910a, htr8910a]

theorem shard_176 {lam p : ℝ} (m : ElevenModel lam p)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr048c : m.d 0 8 < m.d 0 4)
    (htr049c : m.d 0 9 < m.d 0 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr138b : m.d 3 8 < m.d 1 8)
    (htr139b : m.d 3 9 < m.d 1 9)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr239a : m.d 2 3 + lam ≤ m.d 3 9)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr247a : m.d 4 7 + lam ≤ m.d 2 4)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr348c : m.d 3 8 < m.d 3 4)
    (htr349a : m.d 4 9 + lam ≤ m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    : False :=
  proof_shard_176 m htr017a htr017c htr018a htr019a htr024a htr025b htr034c htr035c htr046c htr047c htr048c htr049c htr134a htr135b htr136b htr137b htr138b htr139b htr235b htr236a htr237a htr238a htr239a htr246a htr247a htr248a htr345c htr347a htr348a htr348c htr349a htr356a htr456a htr456c

#print axioms shard_176
end Jsp404.NoSatElevenDBMTerminal
