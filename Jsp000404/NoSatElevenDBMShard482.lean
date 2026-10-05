import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_482 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
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
  have hd810a := (m.hrange 8 10 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr045a, htr046a, htr456b])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr045c, htr056a, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc234zy, htr245c, htr256a, htr345a, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, htr134b, htr145a, htr346a, htr456b])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr345c, htr356a, htr456a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  rcases m.htr 2 4 6 (by decide) (by decide) with
    ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc467yx, htr045a, htr047a, htr245a, htr246a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc468yx, htr045a, htr048a, htr245a, htr246a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567yx, htr245a, htr246a, htr456c, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568yx, htr245a, htr246a, htr456c, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd34a, hd67b, htr245a, htr246a, htr345a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd34a, hd68b, htr245a, htr246a, htr345a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    rcases m.htr 3 6 7 (by decide) (by decide) with
      ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
    ·
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc346yz, htr246a, htr247a, htr367a, htr467b])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd34a, hd78b, htr245a, htr247a, htr345a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd34a, hd79b, htr245a, htr247a, htr345a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc346yz, htr367a, htr467c, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc346yz, htr367b, htr378a, htr467a, htr678a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc014yx, hc478zy, htr013a, htr045a, htr137a, htr245a, htr248a, htr378a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc346yz, htr367a, htr467c, htr479a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hc346yz, htr367b, htr379a, htr467a, htr679a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc014yx, hc789yz, htr013a, htr045a, htr137a, htr379a, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc014yx, hc578zy, htr013a, htr048a, htr137a, htr378a, htr489a, htr589a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd46b, hd78a, htr246a, htr248a, htr489a, htr789a]
      ·
        linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a]
    ·
      have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr247a, htr247b, htr247c, _, _⟩
        linarith only [hlam, hc014yx, hc467zy, htr013a, htr045a, htr136a, htr245a, htr247a, htr367a])
      obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd01b, hd78a, htr013a, htr136a, htr367a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd46b, hd67a, htr246a, htr247a, htr478a, htr678a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc014yx, hc567zy, htr013a, htr047a, htr136a, htr367a, htr478a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc014yx, hc678yz, htr013a, htr045a, htr136a, htr368a, htr457a, htr578a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc346yz, htr246a, htr248a, htr368a, htr468b])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hc789yx, htr247a, htr248a, htr478c, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd34a, hd89b, htr245a, htr248a, htr345a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc014yx, hc567zy, htr013a, htr047a, htr136a, htr367a, htr479a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hc014yx, hc789zy, htr013a, htr045a, htr138a, htr389a, htr457a, htr579a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc346yz, htr368a, htr468c, htr489a, htr689a]
      ·
        linarith only [hlam, hc346yz, htr368b, htr389a, htr468a, htr689a]
  ·
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr045a, htr047a, htr457b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr045c, htr057a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr347a, htr347b, htr347c, _, _⟩
        linarith only [hlam, htr134b, htr145a, htr347a, htr457b])
      obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
      rcases m.htr 2 4 7 (by decide) (by decide) with
        ⟨htr247a, htr247b, htr247c, _, _⟩ | ⟨htr247a, htr247b, htr247c, _, _⟩
      ·
        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
          linarith only [hlam, htr246c, htr247b, htr267c])
        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, htr246b, htr267a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc678yx, htr246a, htr247a, htr467c, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc679yx, htr246a, htr247a, htr467c, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd34a, hd78b, htr245a, htr247a, htr345a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd34a, hd56b, htr245a, htr247a, htr345a, htr467c, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr345a, htr456b, htr468a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
          linarith only [hlam, hc014yx, hc678zy, htr013a, htr045a, htr137a, htr378a, htr456a, htr568a])
        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
        have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr248a, htr248b, htr248c, _, _⟩
          linarith only [hlam, hc347yz, htr247a, htr248a, htr378a, htr478b])
        obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd34a, hd89b, htr245a, htr248a, htr345a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd34a, hd67b, htr345a, htr456b, htr469a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hc014yx, hc689zy, htr013a, htr045a, htr138a, htr389a, htr456a, htr569a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc347yz, htr378a, htr478c, htr489a, htr789a]
        ·
          linarith only [hlam, hc347yz, htr378b, htr389a, htr478a, htr789a]
      ·
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr045a, htr048a, htr458b])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr348a, htr348b, htr348c, _, _⟩
            linarith only [hlam, htr134b, htr145a, htr348a, htr458b])
          obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
          rcases m.htr 2 4 8 (by decide) (by decide) with
            ⟨htr248a, htr248b, htr248c, _, _⟩ | ⟨htr248a, htr248b, htr248c, _, _⟩
          ·
            have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr268a, htr268b, htr268c, _, _⟩
              linarith only [hlam, htr246c, htr248b, htr268c])
            obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
            have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr278a, htr278b, htr278c, _, _⟩
              linarith only [hlam, htr247c, htr248b, htr278c])
            obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, htr246b, htr268a, htr468a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc678xy, htr246a, htr248a, htr467a, htr468c])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, htr247b, htr278a, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd34a, hd56b, htr245a, htr248a, htr345a, htr468c, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd34a, hd68b, htr345a, htr456b, htr467a, htr567a, htr568a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd34a, hd78b, htr345a, htr456a, htr567a, htr678a]
            ·
              linarith only [hlam, hd34a, hd67b, htr245a, htr248a, htr345a, htr478c, htr678a]
          ·
            rcases m.htr 4 5 9 (by decide) (by decide) with
              ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
            ·
              rcases m.htr 2 4 9 (by decide) (by decide) with
                ⟨htr249a, htr249b, htr249c, _, _⟩ | ⟨htr249a, htr249b, htr249c, _, _⟩
              ·
                have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr269a, htr269b, htr269c, _, _⟩
                  linarith only [hlam, htr246c, htr249b, htr269c])
                obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                  linarith only [hlam, htr247c, htr249b, htr279c])
                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                  linarith only [hlam, htr246b, htr269a, htr469a])
                obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc679xy, htr246a, htr249a, htr467a, htr469c])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, htr247b, htr279a, htr479a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hd34a, hd56b, htr245a, htr249a, htr345a, htr469c, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd34a, hd69b, htr345a, htr456b, htr467a, htr567a, htr569a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                rcases m.htr 6 7 9 (by decide) (by decide) with
                  ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                ·
                  linarith only [hlam, hd34a, hd79b, htr345a, htr456a, htr567a, htr679a]
                ·
                  linarith only [hlam, hd34a, hd67b, htr245a, htr249a, htr345a, htr479c, htr679a]
              ·
                rcases m.htr 4 5 10 (by decide) (by decide) with
                  ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                ·
                  rcases m.htr 2 4 10 (by decide) (by decide) with
                    ⟨htr2410a, htr2410b, htr2410c, _, _⟩ | ⟨htr2410a, htr2410b, htr2410c, _, _⟩
                  ·
                    have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
                      linarith only [hlam, htr2410b, htr246c, htr2610c])
                    obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
                    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
                      linarith only [hlam, htr2410b, htr247c, htr2710c])
                    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
                    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                      linarith only [hlam, htr246b, htr2610a, htr4610a])
                    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc6710xy, htr2410a, htr246a, htr4610c, htr467a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                      linarith only [hlam, htr247b, htr2710a, htr4710a])
                    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                      linarith only [hlam, hd34a, hd56b, htr2410a, htr245a, htr345a, htr4610c, htr5610a])
                    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hd34a, hd610b, htr345a, htr456b, htr467a, htr5610a, htr567a])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    rcases m.htr 6 7 10 (by decide) (by decide) with
                      ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    ·
                      linarith only [hlam, hd34a, hd710b, htr345a, htr456a, htr567a, htr6710a]
                    ·
                      linarith only [hlam, hd34a, hd67b, htr2410a, htr245a, htr345a, htr4710c, htr6710a]
                  ·
                    rcases m.htr 5 6 7 (by decide) (by decide) with
                      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                    ·
                      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                        linarith only [hlam, hc014yx, hc678yx, htr013a, htr045a, htr136a, htr368a, htr456a, htr567a])
                      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                        linarith only [hlam, hc014yx, hc679yx, htr013a, htr045a, htr136a, htr369a, htr456a, htr567a])
                      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                        linarith only [hlam, hc234zy, htr246a, htr346b, htr368a, htr468a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                        linarith only [hlam, hc234zy, htr246a, htr346b, htr369a, htr469a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                        linarith only [hlam, hd34a, hd67b, htr345a, htr456b, htr468a, htr567a, htr568a])
                      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                        linarith only [hlam, hc014yx, hc678zy, htr013a, htr045a, htr137a, htr378a, htr456a, htr568a])
                      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc234zy, htr247a, htr347b, htr378a, htr478a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, hd34a, hd67b, htr345a, htr456b, htr469a, htr567a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                        linarith only [hlam, hc014yx, hc689zy, htr013a, htr045a, htr138a, htr389a, htr456a, htr569a])
                      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hd34a, hd78b, htr345a, htr456a, htr567a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd34a, hd89b, htr345a, htr456a, htr568a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hd34a, hd68b, htr345a, htr457b, htr478a, htr689a, htr789a]
                      ·
                        linarith only [hlam, hc367yz, htr378b, htr389a, htr678a, htr789a]
                    ·
                      rcases m.htr 3 6 7 (by decide) (by decide) with
                        ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
                      ·
                        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                          linarith only [hlam, hc234zy, htr046c, htr067a, htr246a, htr346b, htr367a])
                        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                          linarith only [hlam, hc234zy, htr246a, htr346b, htr367a, htr467a])
                        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                          linarith only [hlam, hc234zy, htr246c, htr267a, htr345a, htr456b, htr467a])
                        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                          linarith only [hlam, hd34a, hd68b, htr345a, htr456b, htr467a, htr567a, htr568a])
                        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                        rcases m.htr 4 6 8 (by decide) (by decide) with
                          ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                        ·
                          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                            linarith only [hlam, htr046c, htr068a, htr468a])
                          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                            linarith only [hlam, hc456yz, htr267a, htr268a, htr468a, htr567a])
                          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                            linarith only [hlam, hc014yx, htr013a, htr045a, htr136a, htr368a, htr456b, htr468a])
                          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                          rcases m.htr 4 6 9 (by decide) (by decide) with
                            ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                          ·
                            rcases m.htr 4 6 10 (by decide) (by decide) with
                              ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                            ·
                              rcases m.htr 6 7 8 (by decide) (by decide) with
                                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                              ·
                                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                                  linarith only [hlam, hc014yx, hc789yx, htr013a, htr045a, htr137a, htr379a, htr456b, htr467a, htr678a])
                                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                                have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                                  linarith only [hlam, hc356yz, htr267c, htr279a, htr367b, htr379a, htr567a])
                                obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                                  linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
                                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                                  linarith only [hlam, hd12a, hd78b, htr127a, htr279a, htr578a, htr579a])
                                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                                  linarith only [hlam, hc014yx, hc789zy, htr013a, htr045a, htr138a, htr389a, htr457a, htr579a])
                                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                                  linarith only [hlam, hc356yz, htr368b, htr389a, htr568a, htr689a])
                                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                                rcases m.htr 7 8 9 (by decide) (by decide) with
                                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                                ·
                                  linarith only [hlam, hd34a, hd89b, htr345a, htr456b, htr467a, htr678a, htr789a]
                                ·
                                  linarith only [hlam, hd34a, hd78b, htr345a, htr456b, htr468a, htr689a, htr789a]
                              ·
                                have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                                  linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
                                obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                                  linarith only [hlam, hc014yx, hc789xy, htr013a, htr045a, htr137a, htr378a, htr456b, htr467a, htr679a])
                                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                                  linarith only [hlam, hc356yz, htr367b, htr379a, htr567a, htr679a])
                                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                                  linarith only [hlam, hc014yx, hc789yz, htr013a, htr045a, htr137a, htr379a, htr458a, htr589a])
                                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                                have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                                  linarith only [hlam, hc012yx, hc578zy, htr013a, htr028a, htr137a, htr289a, htr378a, htr589a])
                                obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                                  linarith only [hlam, hc356yz, htr268c, htr289a, htr368b, htr389a, htr568a])
                                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                                rcases m.htr 7 8 9 (by decide) (by decide) with
                                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                                ·
                                  linarith only [hlam, hd01b, hd78a, htr013a, htr138a, htr389a, htr789a]
                                ·
                                  linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a]
                            ·
                              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                                linarith only [hlam, hc056yz, htr0610a, htr4610a, htr467a, htr567a])
                              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                                linarith only [hlam, htr0610c, htr067b, htr0710b])
                              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                              have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                                linarith only [hlam, htr0610c, htr068b, htr0810b])
                              obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                              have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                                linarith only [hlam, hc234zy, htr047c, htr0710a, htr247a, htr347b, htr3710a])
                              obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                              have hforced3810 := (m.htr 3 8 10 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr3810a, htr3810b, htr3810c, _, _⟩
                                linarith only [hlam, hc234zy, htr048c, htr0810a, htr248a, htr348b, htr3810a])
                              obtain ⟨htr3810a, htr3810b, htr3810c, _, _⟩ := hforced3810
                              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                                linarith only [hlam, hc014yx, hc7810yx, htr013a, htr045a, htr137a, htr3710a, htr456b, htr467a, htr678a])
                              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                                linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
                              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                              rcases m.htr 7 8 10 (by decide) (by decide) with
                                ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                              ·
                                linarith only [hlam, hd01b, hd78a, htr013a, htr138a, htr3810a, htr7810a]
                              ·
                                linarith only [hlam, hd01b, hd810a, htr013a, htr137a, htr378a, htr7810a]
                          ·
                            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                              linarith only [hlam, hc056yz, htr069a, htr467a, htr469a, htr567a])
                            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                              linarith only [hlam, htr067b, htr069c, htr079b])
                            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                              linarith only [hlam, htr068b, htr069c, htr089b])
                            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                              linarith only [hlam, hc234zy, htr047c, htr079a, htr247a, htr347b, htr379a])
                            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                            have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                              linarith only [hlam, hc234zy, htr048c, htr089a, htr248a, htr348b, htr389a])
                            obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                              linarith only [hlam, hc014yx, hc789yx, htr013a, htr045a, htr137a, htr379a, htr456b, htr467a, htr678a])
                            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                              linarith only [hlam, hc356yz, htr367b, htr378a, htr567a, htr678a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            rcases m.htr 7 8 9 (by decide) (by decide) with
                              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                            ·
                              linarith only [hlam, hd01b, hd78a, htr013a, htr138a, htr389a, htr789a]
                            ·
                              linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a]
                        ·
                          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                            linarith only [hlam, hc056yz, htr068a, htr467a, htr468a, htr567a])
                          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                            linarith only [hlam, htr067b, htr068c, htr078b])
                          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                          have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                            linarith only [hlam, htr246b, htr268a, htr468a])
                          obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                            linarith only [hlam, hc356yz, htr368a, htr467a, htr468a, htr567a])
                          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                            linarith only [hlam, hc234zy, htr047c, htr078a, htr247a, htr347b, htr378a])
                          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hc014yx, hc789xy, htr013a, htr045a, htr137a, htr378a, htr456b, htr467a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                            linarith only [hlam, hc356yz, htr367b, htr379a, htr567a, htr679a])
                          obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc014yx, hc789yz, htr013a, htr045a, htr137a, htr379a, htr458a, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr289a, htr289b, htr289c, _, _⟩
                            linarith only [hlam, hc012yx, hc568zy, htr013a, htr028a, htr136a, htr289a, htr368a, htr589a])
                          obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd56b, hd78a, htr267a, htr268c, htr289a, htr567a, htr789a]
                          ·
                            linarith only [hlam, hd01b, hd89a, htr013a, htr137a, htr378a, htr789a]
                      ·
                        have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                          linarith only [hlam, hc012yx, htr013a, htr026a, htr136a, htr267a, htr367a])
                        obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hd01b, hd78a, htr013a, htr136a, htr367a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                          linarith only [hlam, hd01b, hd67a, htr013a, htr137a, htr378a, htr678a])
                        obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hc234zy, htr247a, htr347b, htr378a, htr478a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc014yx, hc567zy, htr013a, htr045a, htr136a, htr367a, htr457b, htr478a, htr578a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                          linarith only [hlam, hc014yx, hc678yz, htr013a, htr045a, htr136a, htr368a, htr457a, htr578a])
                        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc014yx, hc789yx, htr013a, htr045a, htr137a, htr379a, htr457a, htr578a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                          linarith only [hlam, hc234zy, htr246a, htr346b, htr368a, htr468a])
                        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                        have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                          linarith only [hlam, hc234zy, htr246c, htr268a, htr345a, htr456b, htr468a])
                        obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                        have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr279a, htr279b, htr279c, _, _⟩
                          linarith only [hlam, hc678xy, htr267c, htr268a, htr279a, htr367b, htr379a])
                        obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hc012yx, hc567zy, htr013a, htr027a, htr136a, htr279a, htr367a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                          linarith only [hlam, hc014yx, hc789zy, htr013a, htr045a, htr138a, htr389a, htr457a, htr579a])
                        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc678xy, htr367a, htr368b, htr389a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd34a, hd89b, htr345a, htr457a, htr578a, htr789a]
                        ·
                          linarith only [hlam, hd67a, hd78b, htr367a, htr368a, htr689a, htr789a]
                ·
                  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                    linarith only [hlam, hc234zy, htr015b, htr0510a, htr135b, htr245a, htr345b, htr4510a])
                  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                    linarith only [hlam, htr0510c, htr056b, htr0610b])
                  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                    linarith only [hlam, htr0510c, htr057b, htr0710b])
                  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                    linarith only [hlam, hc234zy, htr245a, htr345b, htr3510a, htr4510a])
                  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
                  have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
                    linarith only [hlam, hc234zy, htr046c, htr0610a, htr246a, htr346b, htr3610a])
                  obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
                  have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                    linarith only [hlam, hc234zy, htr047c, htr0710a, htr247a, htr347b, htr3710a])
                  obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                    linarith only [hlam, hc014yx, hc6710yx, htr013a, htr045a, htr136a, htr3610a, htr456a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                    linarith only [hlam, hc5610yx, htr3510a, htr356b, htr367a, htr567a])
                  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                  rcases m.htr 6 7 10 (by decide) (by decide) with
                    ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                  ·
                    linarith only [hlam, hd01b, hd67a, htr013a, htr137a, htr3710a, htr6710a]
                  ·
                    linarith only [hlam, hd01b, hd710a, htr013a, htr136a, htr367a, htr6710a]
            ·
              have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                linarith only [hlam, hc234zy, htr015b, htr059a, htr135b, htr245a, htr345b, htr459a])
              obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, htr056b, htr059c, htr069b])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, htr057b, htr059c, htr079b])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr359a, htr359b, htr359c, _, _⟩
                linarith only [hlam, hc234zy, htr245a, htr345b, htr359a, htr459a])
              obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
              have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                linarith only [hlam, hc234zy, htr046c, htr069a, htr246a, htr346b, htr369a])
              obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hc234zy, htr047c, htr079a, htr247a, htr347b, htr379a])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hc014yx, hc679yx, htr013a, htr045a, htr136a, htr369a, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hc569yx, htr356b, htr359a, htr367a, htr567a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              rcases m.htr 6 7 9 (by decide) (by decide) with
                ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
              ·
                linarith only [hlam, hd01b, hd67a, htr013a, htr137a, htr379a, htr679a]
              ·
                linarith only [hlam, hd01b, hd79a, htr013a, htr136a, htr367a, htr679a]
        ·
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc234zy, htr015b, htr058a, htr135b, htr245a, htr345b, htr458a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr056b, htr058c, htr068b])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr057b, htr058c, htr078b])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr358a, htr358b, htr358c, _, _⟩
            linarith only [hlam, hc234zy, htr245a, htr345b, htr358a, htr458a])
          obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, hc234zy, htr046c, htr068a, htr246a, htr346b, htr368a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr378a, htr378b, htr378c, _, _⟩
            linarith only [hlam, hc234zy, htr047c, htr078a, htr247a, htr347b, htr378a])
          obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
            linarith only [hlam, hc014yx, hc678yx, htr013a, htr045a, htr136a, htr368a, htr456a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr367a, htr367b, htr367c, _, _⟩
            linarith only [hlam, hc568yx, htr356b, htr358a, htr367a, htr567a])
          obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd01b, hd67a, htr013a, htr137a, htr378a, htr678a]
          ·
            linarith only [hlam, hd01b, hd78a, htr013a, htr136a, htr367a, htr678a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc567yx, htr045a, htr047a, htr456a, htr457b])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc234zy, htr015b, htr057a, htr135b, htr245a, htr345b, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr056b, htr057c, htr067b])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, htr245b, htr257a, htr457a])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, hc234zy, htr245a, htr345b, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, hc234zy, htr046c, htr067a, htr246a, htr346b, htr367a])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc014yx, hc678xy, htr013a, htr045a, htr136a, htr367a, htr456a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc567yx, htr056b, htr057a, htr068a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr248a, htr248b, htr248c, _, _⟩
        linarith only [hlam, hc468zy, htr046c, htr068a, htr246a, htr248a])
      obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc567yx, htr356b, htr357a, htr368a, htr568a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc014yx, hc679xy, htr013a, htr045a, htr136a, htr367a, htr456a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hc567yx, htr356b, htr357a, htr369a, htr569a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd01b, hd78a, htr013a, htr135a, htr357a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc567yx, htr047c, htr078a, htr456a, htr457c, htr578a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr047b, htr048c, htr078b])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hc567yx, htr256a, htr257c, htr278a, htr578a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, htr014b, htr048a, htr134b, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd01b, hd89a, htr013a, htr136a, htr368a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr389a, htr389b, htr389c, _, _⟩
        linarith only [hlam, hd01b, hd68a, htr013a, htr138a, htr389a, htr689a])
      obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc234zy, htr248a, htr348b, htr389a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc012yx, hc689yz, htr013a, htr027a, htr136a, htr278a, htr369a, htr789a]
      ·
        linarith only [hlam, hc014yx, hc678yz, htr013a, htr048a, htr136a, htr368a, htr489a, htr789a]

theorem shard_482 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr026a : m.d 0 2 + lam ≤ m.d 2 6)
    (htr027a : m.d 0 2 + lam ≤ m.d 2 7)
    (htr028a : m.d 0 2 + lam ≤ m.d 2 8)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245b : m.d 4 5 < m.d 2 5)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    : False :=
  proof_shard_482 m htr013a htr014b htr015b htr026a htr027a htr028a htr045a htr045c htr127a htr134b htr135a htr135b htr136a htr137a htr138a htr145a htr245a htr245b htr245c htr345a htr345b htr345c htr456a htr456b htr456c

#print axioms shard_482
end Jsp404.NoSatElevenDBMTerminal
