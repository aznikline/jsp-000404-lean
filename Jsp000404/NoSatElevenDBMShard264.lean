import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_264 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd13a := (m.hrange 1 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
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
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc135xy, hc135yx, hc135yz, hc135zy⟩ := endpoint_caps m 1 3 5 (by decide) (by decide)
  obtain ⟨hc136xy, hc136yx, hc136yz, hc136zy⟩ := endpoint_caps m 1 3 6 (by decide) (by decide)
  obtain ⟨hc137xy, hc137yx, hc137yz, hc137zy⟩ := endpoint_caps m 1 3 7 (by decide) (by decide)
  obtain ⟨hc138xy, hc138yx, hc138yz, hc138zy⟩ := endpoint_caps m 1 3 8 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc268xy, hc268yx, hc268yz, hc268zy⟩ := endpoint_caps m 2 6 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6810xy, hc6810yx, hc6810yz, hc6810zy⟩ := endpoint_caps m 6 8 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, htr024b, htr034c, htr245a, htr345a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd13a, hd56b, htr013a, htr014a, htr134c, htr345a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hd13a, hd45b, htr013a, htr015a, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd13a, hd57b, htr013a, htr014a, htr134c, htr345a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hd13a, hd45b, htr013a, htr015a, htr157a, htr457a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd13a, hd58b, htr013a, htr014a, htr134c, htr345a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hd13a, hd45b, htr013a, htr015a, htr158a, htr458a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd13a, hd67b, htr013a, htr014a, htr134c, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hd13a, hd46b, htr013a, htr016a, htr167a, htr467a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd13a, hd68b, htr013a, htr014a, htr134c, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
      linarith only [hlam, hd13a, hd46b, htr013a, htr016a, htr168a, htr468a])
    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd13a, hd78b, htr013a, htr014a, htr134c, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd13a, hd79b, htr013a, htr014a, htr134c, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      rcases m.htr 5 6 7 (by decide) (by decide) with
        ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
      ·
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc245yz, htr256a, htr456c, htr467a, htr567a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc135xy, hc456zy, htr013a, htr014a, htr134c, htr157a, htr256a, htr257a, htr346a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc456zy, htr467c, htr478a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc136xy, hc457zy, htr013a, htr014a, htr134c, htr167a, htr347a, htr578a, htr678a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc123yx, hc478zy, htr013a, htr014a, htr125a, htr148a, htr257a, htr578a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc456zy, htr467c, htr479a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc136xy, hc457zy, htr013a, htr014a, htr134c, htr167a, htr347a, htr579a, htr679a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc123yx, hc789yz, htr013a, htr018a, htr125a, htr189a, htr257a, htr579a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc458yx, htr134c, htr148c, htr189a, htr345a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd45b, hd78a, htr134c, htr148a, htr345a, htr489a, htr789a]
        ·
          linarith only [hlam, hd12b, hd89a, htr125a, htr257a, htr578a, htr789a]
      ·
        have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr256a, htr256b, htr256c, _, _⟩
          linarith only [hlam, hc123yx, hc467zy, htr013a, htr014a, htr125a, htr134c, htr256a, htr347a, htr567a])
        obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc135xy, hc457zy, htr013a, htr014a, htr134c, htr156a, htr256a, htr257a, htr347a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc245yz, htr257a, htr457c, htr478a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hc245yz, htr257a, htr457c, htr479a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hc135xy, hc467zy, htr013a, htr014a, htr134c, htr157a, htr347a, htr578a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc135xy, hc478zy, htr013a, htr014a, htr148a, htr156a, htr567a, htr678a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc245yz, htr134c, htr148a, htr258a, htr345a, htr458b])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45b, hd89a, htr256a, htr258a, htr456a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd45b, hd58a, htr134c, htr148a, htr345a, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc458yx, htr134c, htr148c, htr189a, htr345a, htr489a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc135xy, hc467zy, htr013a, htr014a, htr134c, htr157a, htr347a, htr579a, htr679a]
        ·
          linarith only [hlam, hc135xy, hc789yz, htr013a, htr018a, htr156a, htr189a, htr567a, htr679a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hd13a, hd45b, htr013a, htr014b, htr047a, htr345a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc245yz, htr257a, htr345a, htr347a, htr457b])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc456zy, htr346a, htr347a, htr467b, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      rcases m.htr 2 5 6 (by decide) (by decide) with
        ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
      ·
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc457yx, htr245b, htr247a, htr256a, htr456a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc245yz, htr256a, htr456c, htr468a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd45b, hd78a, htr256a, htr257a, htr456a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd45b, hd57a, htr345a, htr347a, htr478a, htr578a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc135xy, hc578yz, htr013a, htr017a, htr156a, htr178a, htr256a, htr258a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc245yz, htr034c, htr048a, htr258a, htr345a, htr458b])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc789yx, htr047a, htr048a, htr478c, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc457yx, htr137c, htr179a, htr345a, htr347c, htr479a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd24a, hd89b, htr047a, htr048a, htr247a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc245yz, htr258a, htr458c, htr489a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc135xy, hc678yz, htr013a, htr017a, htr158a, htr178a, htr589a, htr689a]
        ·
          linarith only [hlam, hc135xy, hc789zy, htr013a, htr017a, htr156a, htr179a, htr568a, htr689a]
      ·
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc135xy, hc456zy, htr013a, htr014a, htr134c, htr158a, htr256a, htr258a, htr346a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
          linarith only [hlam, hd12b, hd78a, htr125a, htr256a, htr567a, htr678a])
        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc123yx, hc678yz, htr013a, htr017a, htr125a, htr178a, htr256a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc456zy, htr034c, htr048a, htr346a, htr468b, htr568a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr148a, htr148b, htr148c, _, _⟩
          linarith only [hlam, hc457yx, htr047a, htr048a, htr134c, htr148a, htr345a])
        obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc789yx, htr047a, htr048a, htr478c, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc457yx, htr137c, htr179a, htr345a, htr347c, htr479a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd13a, hd89b, htr013a, htr014a, htr148a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc123yx, hc789zy, htr013a, htr017a, htr125a, htr179a, htr258a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc456zy, htr468c, htr489a, htr568a, htr689a]
        ·
          linarith only [hlam, hc136xy, hc578yz, htr013a, htr017a, htr168a, htr178a, htr589a, htr689a]
  ·
    have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr046a, htr046b, htr046c, _, _⟩
      linarith only [hlam, hd13a, hd45b, htr013a, htr014b, htr046a, htr345a, htr346a])
    obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
    have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr256a, htr256b, htr256c, _, _⟩
      linarith only [hlam, hc245yz, htr256a, htr345a, htr346a, htr456b])
    obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, htr034c, htr047a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr046c, htr047b, htr067c])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
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
        linarith only [hlam, hc456yx, htr136c, htr168a, htr345a, htr346c, htr468a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc679yx, htr034c, htr046a, htr347a, htr467c, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc456yx, htr136c, htr169a, htr345a, htr346c, htr469a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
        linarith only [hlam, hc6710yx, htr034c, htr046a, htr347a, htr4610a, htr467c])
      obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
      have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
        linarith only [hlam, hc456yx, htr136c, htr1610a, htr345a, htr346c, htr4610a])
      obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd13a, hd78b, htr013a, htr014a, htr134c, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc467xy, htr046a, htr047b, htr078a, htr478a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, htr467c, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd13a, hd89b, htr013a, htr016a, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd13a, hd68b, htr013a, htr018a, htr189a, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
        linarith only [hlam, hd13a, hd810b, htr013a, htr016a, htr168a, htr6810a])
      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
        linarith only [hlam, hd13a, hd68b, htr013a, htr018a, htr1810a, htr6810a])
      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc123yx, hc678zy, htr013a, htr016a, htr128a, htr168a, htr289a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc138xy, hc6810zy, htr013a, htr016a, htr1610a, htr189a, htr2810a, htr289a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc123yx, hc678zy, htr013a, htr016a, htr125a, htr168a, htr257a, htr578a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc135xy, hc568yz, htr013a, htr016a, htr157a, htr168a, htr257a, htr258a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 5 8 10 (by decide) (by decide) with
          ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
        ·
          linarith only [hlam, hd56a, hd68b, htr256a, htr258a, htr5810a, htr6810a]
        ·
          linarith only [hlam, hc135xy, hc268yz, htr013a, htr016a, htr158a, htr168a, htr2810a, htr5810a]
      ·
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc123yx, hc268yz, htr012c, htr013a, htr016a, htr027c, htr078a, htr168a, htr289a, htr789a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
          linarith only [hlam, hc138xy, hc689zy, htr013a, htr016a, htr169a, htr1810a, htr2810a, htr289a])
        obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hc135xy, hc689zy, htr013a, htr016a, htr157a, htr169a, htr578a, htr789a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr257a, htr257b, htr257c, _, _⟩
          linarith only [hlam, hc245yz, htr257a, htr457c, htr478a, htr578a])
        obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
        have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr258a, htr258b, htr258c, _, _⟩
          linarith only [hlam, hc135xy, hc457zy, htr013a, htr014a, htr134c, htr158a, htr257a, htr258a, htr347a])
        obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
        rcases m.htr 5 8 10 (by decide) (by decide) with
          ⟨htr5810a, htr5810b, htr5810c, _, _⟩ | ⟨htr5810a, htr5810b, htr5810c, _, _⟩
        ·
          linarith only [hlam, hc123yx, hc568yz, htr013a, htr016a, htr128a, htr168a, htr2810a, htr5810a]
        ·
          linarith only [hlam, hc123yx, hc6810zy, htr013a, htr016a, htr125a, htr1610a, htr258a, htr5810a]
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc456yx, htr046a, htr047a, htr345a, htr347a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr257a, htr257b, htr257c, _, _⟩
        linarith only [hlam, hc245yz, htr257a, htr345a, htr347a, htr457b])
      obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
      rcases m.htr 2 4 6 (by decide) (by decide) with
        ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
      ·
        rcases m.htr 3 4 8 (by decide) (by decide) with
          ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
        ·
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr034c, htr048a, htr348a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr046c, htr048b, htr068c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr047c, htr048b, htr078c])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc137xy, htr013a, htr017b, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr468a, htr468b, htr468c, _, _⟩
            linarith only [hlam, htr046b, htr068a, htr468a])
          obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc678xy, htr034c, htr046a, htr348a, htr467a, htr468c])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd13a, hd78b, htr013a, htr016a, htr167a, htr678a]
          ·
            linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr178a, htr678a]
        ·
          rcases m.htr 3 4 9 (by decide) (by decide) with
            ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
          ·
            have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr049a, htr049b, htr049c, _, _⟩
              linarith only [hlam, htr034c, htr049a, htr349a])
            obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr046c, htr049b, htr069c])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, htr047c, htr049b, htr079c])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc137xy, htr013a, htr017b, htr079a, htr179a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr469a, htr469b, htr469c, _, _⟩
              linarith only [hlam, htr046b, htr069a, htr469a])
            obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc679xy, htr034c, htr046a, htr349a, htr467a, htr469c])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              linarith only [hlam, hd13a, hd79b, htr013a, htr016a, htr167a, htr679a]
            ·
              linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr179a, htr679a]
          ·
            rcases m.htr 3 4 10 (by decide) (by decide) with
              ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
            ·
              have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                linarith only [hlam, htr034c, htr0410a, htr3410a])
              obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                linarith only [hlam, htr0410b, htr046c, htr0610c])
              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, htr0410b, htr047c, htr0710c])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hc137xy, htr013a, htr017b, htr0710a, htr1710a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                linarith only [hlam, htr046b, htr0610a, htr4610a])
              obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc6710xy, htr034c, htr046a, htr3410a, htr4610c, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              rcases m.htr 6 7 10 (by decide) (by decide) with
                ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              ·
                linarith only [hlam, hd13a, hd710b, htr013a, htr016a, htr167a, htr6710a]
              ·
                linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr1710a, htr6710a]
            ·
              rcases m.htr 4 6 7 (by decide) (by decide) with
                ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hc123yx, hc678yx, htr013a, htr016a, htr125a, htr167a, htr256a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hd45b, hd56a, htr345a, htr346a, htr468a, htr568a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc456yx, htr136c, htr168a, htr345a, htr346c, htr468a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hc123yx, hc678zy, htr013a, htr016a, htr125a, htr168a, htr257a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hd45b, hd57a, htr345a, htr347a, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd13a, hd78b, htr013a, htr016a, htr167a, htr678a]
                ·
                  linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr178a, htr678a]
              ·
                have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr267a, htr267b, htr267c, _, _⟩
                  linarith only [hlam, hd26a, hd45b, htr267a, htr345a, htr346a, htr467a])
                obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd45b, hd56a, htr345a, htr346a, htr467a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc123yx, hc678xy, htr013a, htr016a, htr125a, htr168a, htr256a, htr567a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr268a, htr268b, htr268c, _, _⟩
                  linarith only [hlam, hd45b, hd67a, htr136c, htr168a, htr267a, htr268a, htr345a, htr346c])
                obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd45b, hd67a, htr246c, htr268a, htr345a, htr346a, htr567a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc123yx, hc678yz, htr013a, htr017a, htr125a, htr178a, htr256a, htr568a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a]
                ·
                  linarith only [hlam, hd45b, hd78a, htr345a, htr346a, htr467a, htr678a]
      ·
        have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr247a, htr247b, htr247c, _, _⟩
          linarith only [hlam, hc456yx, htr246a, htr247a, htr345a, htr347a])
        obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
        rcases m.htr 3 4 8 (by decide) (by decide) with
          ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
        ·
          have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr048a, htr048b, htr048c, _, _⟩
            linarith only [hlam, htr034c, htr048a, htr348a])
          obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr046c, htr048b, htr068c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr047c, htr048b, htr078c])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
            linarith only [hlam, hc136xy, htr013a, htr016b, htr068a, htr168a])
          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc137xy, htr013a, htr017b, htr078a, htr178a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc123yx, hc678xy, htr013a, htr016a, htr124a, htr168a, htr246a, htr467a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd13a, hd78b, htr013a, htr016a, htr167a, htr678a]
          ·
            linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr178a, htr678a]
        ·
          rcases m.htr 3 4 9 (by decide) (by decide) with
            ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
          ·
            have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr049a, htr049b, htr049c, _, _⟩
              linarith only [hlam, htr034c, htr049a, htr349a])
            obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, htr046c, htr049b, htr069c])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, htr047c, htr049b, htr079c])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr169a, htr169b, htr169c, _, _⟩
              linarith only [hlam, hc136xy, htr013a, htr016b, htr069a, htr169a])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
              linarith only [hlam, hc137xy, htr013a, htr017b, htr079a, htr179a])
            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc123yx, hc679xy, htr013a, htr016a, htr124a, htr169a, htr246a, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 6 7 9 (by decide) (by decide) with
              ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
            ·
              linarith only [hlam, hd13a, hd79b, htr013a, htr016a, htr167a, htr679a]
            ·
              linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr179a, htr679a]
          ·
            rcases m.htr 3 4 10 (by decide) (by decide) with
              ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
            ·
              have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
                linarith only [hlam, htr034c, htr0410a, htr3410a])
              obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                linarith only [hlam, htr0410b, htr046c, htr0610c])
              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                linarith only [hlam, htr0410b, htr047c, htr0710c])
              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
              have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                linarith only [hlam, hc136xy, htr013a, htr016b, htr0610a, htr1610a])
              obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                linarith only [hlam, hc137xy, htr013a, htr017b, htr0710a, htr1710a])
              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
              have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                linarith only [hlam, hc123yx, hc6710xy, htr013a, htr016a, htr124a, htr1610a, htr246a, htr467a])
              obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc456yx, htr136c, htr167a, htr345a, htr346c, htr467a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              rcases m.htr 6 7 10 (by decide) (by decide) with
                ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
              ·
                linarith only [hlam, hd13a, hd710b, htr013a, htr016a, htr167a, htr6710a]
              ·
                linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr1710a, htr6710a]
            ·
              rcases m.htr 3 6 7 (by decide) (by decide) with
                ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
              ·
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc123yx, hc678yx, htr013a, htr016a, htr124a, htr136c, htr246a, htr367a, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc456yx, htr136c, htr168a, htr345a, htr346c, htr468a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc123yx, hc678zy, htr013a, htr016a, htr124a, htr168a, htr247a, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd13a, hd78b, htr013a, htr016a, htr136c, htr367a, htr678a]
                ·
                  linarith only [hlam, hd13a, hd67b, htr013a, htr017a, htr178a, htr678a]
              ·
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc456yx, htr345a, htr346c, htr367a, htr467a])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc123yx, hc678xy, htr013a, htr016a, htr124a, htr168a, htr246a, htr467a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                  linarith only [hlam, hc456yx, htr136c, htr168a, htr345a, htr346c, htr468a])
                obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc123yx, hc678yz, htr013a, htr017a, htr124a, htr178a, htr246a, htr468a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc457yx, htr137c, htr178a, htr345a, htr347c, htr478a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                rcases m.htr 6 7 8 (by decide) (by decide) with
                  ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                ·
                  linarith only [hlam, hd45b, hd67a, htr345a, htr347a, htr478a, htr678a]
                ·
                  linarith only [hlam, hd45b, hd78a, htr345a, htr346a, htr467a, htr678a]

theorem shard_264 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014b : m.d 0 1 < m.d 0 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_264 m htr012c htr013a htr014a htr014b htr015a htr016a htr016b htr017a htr017b htr018a htr024b htr027c htr034c htr124a htr125a htr128a htr134c htr136c htr137c htr345a

#print axioms shard_264
end Jsp404.NoSatElevenDBMTerminal
