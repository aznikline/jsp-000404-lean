import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_177 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr048c : m.d 0 8 < m.d 0 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr348c : m.d 3 8 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd79a := (m.hrange 7 9 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr045b, htr056a, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr015c, htr045b, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd13b, hd67a, htr134a, htr345a, htr456a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd13b, hd68a, htr134a, htr345a, htr456a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  rcases m.htr 4 5 7 (by decide) (by decide) with
    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hd13b, hd56a, htr034c, htr045c, htr057a, htr134a, htr456a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd13b, hd56a, htr134a, htr345c, htr357a, htr456a, htr457a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, hc123zy, htr135c, htr157a, htr235a, htr357a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hc567xy, htr156c, htr157a, htr168a, htr568a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc567xy, htr057a, htr058a, htr456a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc567xy, htr157a, htr158a, htr456a, htr458a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      rcases m.htr 4 5 9 (by decide) (by decide) with
        ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
      ·
        rcases m.htr 4 5 10 (by decide) (by decide) with
          ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
        ·
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc123zy, hc789yx, htr134a, htr235a, htr347a, htr357a, htr479a, htr578a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hc567xy, htr456a, htr457b, htr479a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hc123zy, hc789zy, htr134a, htr235a, htr348a, htr357a, htr489a, htr579a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc568xy, htr456a, htr458b, htr489a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd56a, hd89b, htr456a, htr457a, htr578a, htr789a]
            ·
              linarith only [hlam, hd56a, hd78b, htr456a, htr458a, htr589a, htr789a]
          ·
            have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr579a, htr579b, htr579c, _, _⟩
              linarith only [hlam, hc123zy, hc789xy, htr134a, htr235a, htr347a, htr357a, htr478a, htr579a])
            obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
            have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr479a, htr479b, htr479c, _, _⟩
              linarith only [hlam, hc567xy, htr456a, htr457b, htr479a, htr579a])
            obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc123zy, hc789yz, htr134a, htr135b, htr158a, htr235a, htr347a, htr479a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr489a, htr489b, htr489c, _, _⟩
              linarith only [hlam, hc568xy, htr456a, htr458b, htr489a, htr589a])
            obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd13b, hd78a, htr134a, htr348a, htr489a, htr789a]
            ·
              linarith only [hlam, hd13b, hd89a, htr134a, htr347a, htr478a, htr789a]
        ·
          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
            linarith only [hlam, htr045b, htr0510a, htr4510a])
          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
            linarith only [hlam, htr0510c, htr057b, htr0710b])
          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
            linarith only [hlam, htr0510c, htr058b, htr0810b])
          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, hd13b, hd56a, htr034c, htr047c, htr0710a, htr134a, htr456a, htr457b, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
            linarith only [hlam, hd13b, hd56a, htr034c, htr048c, htr0810a, htr134a, htr456a, htr458b, htr4810a])
          obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc123zy, hc7810yx, htr134a, htr235a, htr347a, htr357a, htr4710a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          rcases m.htr 7 8 10 (by decide) (by decide) with
            ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          ·
            linarith only [hlam, hd13b, hd78a, htr134a, htr348a, htr4810a, htr7810a]
          ·
            linarith only [hlam, hd13b, hd810a, htr134a, htr347a, htr478a, htr7810a]
      ·
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, htr045b, htr059a, htr459a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, htr057b, htr059c, htr079b])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, htr058b, htr059c, htr089b])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd13b, hd56a, htr034c, htr047c, htr079a, htr134a, htr456a, htr457b, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd13b, hd56a, htr034c, htr048c, htr089a, htr134a, htr456a, htr458b, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc123zy, hc789yx, htr134a, htr235a, htr347a, htr357a, htr479a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd13b, hd78a, htr134a, htr348a, htr489a, htr789a]
        ·
          linarith only [hlam, hd13b, hd89a, htr134a, htr347a, htr478a, htr789a]
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr045b, htr058a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr057b, htr058c, htr078b])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, htr015c, htr045b, htr158a, htr458a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd13b, hd56a, htr034c, htr047c, htr078a, htr134a, htr456a, htr457b, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc123zy, hc789xy, htr134a, htr235a, htr347a, htr357a, htr478a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc567xy, htr456a, htr457b, htr479a, htr579a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd13b, hd89a, htr134a, htr345a, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc578yx, htr157a, htr158c, htr189a, htr589a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc123zy, hc789yz, htr134a, htr136b, htr168a, htr236a, htr347a, htr479a, htr689a]
      ·
        linarith only [hlam, hc012xy, hc568yz, htr018a, htr024a, htr189a, htr245a, htr458a, htr689a]
  ·
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr015c, htr045b, htr157a, htr457a])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd13b, hd78a, htr134a, htr345a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd13b, hd79a, htr134a, htr345a, htr457a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr358a, htr358b, htr358c, _, _⟩
        linarith only [hlam, hd13b, hd56a, htr134a, htr345c, htr358a, htr456a, htr458a])
      obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc123zy, htr135c, htr158a, htr235a, htr358a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc568xy, htr156c, htr158a, htr167a, htr567a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc578xy, htr157c, htr158a, htr179a, htr579a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc567yz, htr457a, htr458a, htr578c, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc012xy, hc567yz, htr017a, htr024a, htr179a, htr245a, htr457a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc123zy, hc789zy, htr134a, htr136b, htr167a, htr236a, htr348a, htr489a, htr679a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc568xy, htr456a, htr458b, htr489a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd01a, hd89b, htr016a, htr167a, htr678a, htr789a]
      ·
        linarith only [hlam, hd56a, hd78b, htr456a, htr458a, htr589a, htr789a]
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd13b, hd89a, htr134a, htr345a, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      rcases m.htr 3 6 7 (by decide) (by decide) with
        ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
      ·
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc123zy, htr136c, htr167a, htr236a, htr367a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc123zy, hc578yz, htr134a, htr236a, htr345a, htr367a, htr458a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc567yz, htr167a, htr168a, htr578a, htr678b])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc012xy, hc567yz, htr017a, htr024a, htr178a, htr245a, htr457a, htr678a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, hc579xy, htr157c, htr159a, htr178a, htr578a])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr359a, htr359b, htr359c, _, _⟩
          linarith only [hlam, hc123zy, htr135c, htr159a, htr235a, htr359a])
        obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hd13b, hd56a, htr134a, htr345c, htr359a, htr456a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc012xy, hc589yz, htr016a, htr024a, htr168a, htr245a, htr459a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
        ·
          linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]
      ·
        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
          linarith only [hlam, hc123zy, htr026b, htr067a, htr134a, htr236b, htr346c, htr367a])
        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc569xy, htr056c, htr059a, htr067a, htr567a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, htr136b, htr167a, htr367a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hd13b, hd56a, htr034c, htr045c, htr059a, htr134a, htr456a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd13b, hd910a, htr134a, htr345a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd13b, hd57a, htr134a, htr346c, htr367a, htr578a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc156zy, htr167c, htr178a, htr567a, htr678a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hd13b, hd57a, htr134a, htr346c, htr367a, htr579a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc012xy, hc589yz, htr017a, htr024a, htr178a, htr245a, htr459a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc123zy, hc578yz, htr134a, htr238a, htr345a, htr389a, htr458a, htr789a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd13b, hd56a, htr134a, htr348c, htr389a, htr568a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hd13b, hd58a, htr034c, htr046c, htr068a, htr134a, htr589a, htr689a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
          linarith only [hlam, hc568yz, htr068a, htr069a, htr589a, htr689b])
        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd56a, hd910b, htr067a, htr069a, htr567a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc578yz, htr589a, htr679c, htr6910a, htr789c, htr8910a]
        ·
          linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]

theorem shard_177 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr048c : m.d 0 8 < m.d 0 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236b : m.d 2 3 < m.d 2 6)
    (htr238a : m.d 2 3 + lam ≤ m.d 3 8)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 4 8 + lam ≤ m.d 3 4)
    (htr348c : m.d 3 8 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_177 m htr015c htr016a htr017a htr018a htr024a htr026b htr034c htr045b htr045c htr046c htr047c htr048c htr134a htr135b htr135c htr136b htr136c htr235a htr236a htr236b htr238a htr245a htr345a htr345c htr346c htr347a htr348a htr348c htr456a

#print axioms shard_177
end Jsp404.NoSatElevenDBMTerminal
