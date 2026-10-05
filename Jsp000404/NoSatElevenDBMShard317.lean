import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_317 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd04a, hd04braw⟩ := m.hrange 0 4 (by decide)
  have hd04b : m.d 0 4 < 4*lam := by
    linarith only [hd04braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd15a, hd15braw⟩ := m.hrange 1 5 (by decide)
  have hd15b : m.d 1 5 < 4*lam := by
    linarith only [hd15braw, hp]
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < 4*lam := by
    linarith only [hd17braw, hp]
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd48a := (m.hrange 4 8 (by decide)).1
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
  obtain ⟨hd510a, hd510braw⟩ := m.hrange 5 10 (by decide)
  have hd510b : m.d 5 10 < 4*lam := by
    linarith only [hd510braw, hp]
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
  obtain ⟨hc045xy, hc045yx, hc045yz, hc045zy⟩ := endpoint_caps m 0 4 5 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
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
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr036a, htr036b, htr036c, _, _⟩
      linarith only [hlam, hc456xy, htr034a, htr036a, htr345a, htr346c])
    obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, htr345c, htr346b, htr356c])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, htr345b, htr356a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr156a, htr156b, htr156c, _, _⟩
      linarith only [hlam, hc145zy, htr156a, htr345a, htr346a, htr456c])
    obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567yx, htr345a, htr346a, htr456c, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568yx, htr345a, htr346a, htr456c, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr012a, htr015a, htr156a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr167a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc126xy, htr012a, htr016b, htr067a, htr167a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, htr036c, htr037b, htr067c])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr467a, htr567a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc456xy, htr345a, htr346b, htr367a, htr467a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
      linarith only [hlam, hd12a, hd68b, htr012a, htr015a, htr156a, htr568a])
    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd45a, hd56b, htr345a, htr346a, htr468a, htr568a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr368a, htr368b, htr368c, _, _⟩
      linarith only [hlam, hc456xy, htr345a, htr346b, htr368a, htr468a])
    obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc145zy, htr157a, htr345a, htr347a, htr457c])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr012a, htr015a, htr157a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd45a, hd57b, htr345a, htr347a, htr478a, htr578a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc457xy, htr345a, htr347b, htr378a, htr478a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd12a, hd79b, htr012a, htr015a, htr157a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd45a, hd57b, htr345a, htr347a, htr479a, htr579a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, hc457xy, htr345a, htr347b, htr379a, htr479a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc123xy, hc567zy, htr012a, htr013c, htr015a, htr037a, htr157a, htr378a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr158a, htr158b, htr158c, _, _⟩
        linarith only [hlam, hc123xy, hc578zy, htr012a, htr013c, htr015a, htr036a, htr158a, htr367a, htr678a])
      obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc125xy, htr012a, htr015b, htr058a, htr158a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr046a, htr046b, htr046c, _, _⟩
        linarith only [hlam, hc456xy, htr045c, htr046a, htr058a, htr458a])
      obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc145zy, htr158a, htr345a, htr348a, htr458c])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd04b, hd89a, htr046a, htr347a, htr348a, htr467c, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd48a, hd56b, htr156a, htr158a, htr489a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc568yx, htr156a, htr158c, htr189a, htr589a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      rcases m.htr 6 7 9 (by decide) (by decide) with
        ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
      ·
        linarith only [hlam, hc123xy, hc567zy, htr012a, htr013c, htr015a, htr037a, htr157a, htr379a, htr679a]
      ·
        linarith only [hlam, hc123xy, hc789yz, htr012a, htr013c, htr018a, htr036a, htr189a, htr367a, htr679a]
    ·
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, hc123xy, htr012a, htr014a, htr134a, htr147a, htr347a])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      rcases m.htr 2 4 6 (by decide) (by decide) with
        ⟨htr246a, htr246b, htr246c, _, _⟩ | ⟨htr246a, htr246b, htr246c, _, _⟩
      ·
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hc456xy, htr125c, htr157a, htr245c, htr246a, htr457a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc456xy, htr125c, htr158a, htr245c, htr246a, htr458a])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc123xy, hc578zy, htr012a, htr015a, htr134a, htr158a, htr347a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc467yx, htr124c, htr147c, htr178a, htr246a, htr478a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        rcases m.htr 5 7 8 (by decide) (by decide) with
          ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd78b, htr012a, htr015a, htr157a, htr578a]
        ·
          linarith only [hlam, hd12a, hd57b, htr012a, htr017a, htr178a, htr578a]
      ·
        have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr146a, htr146b, htr146c, _, _⟩
          linarith only [hlam, hd12a, hd24b, htr012a, htr014a, htr146a, htr246a])
        obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
        have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr157a, htr157b, htr157c, _, _⟩
          linarith only [hlam, hc124xy, hc457yz, htr012a, htr015a, htr146a, htr157a, htr346a, htr347a])
        obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
        have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr057a, htr057b, htr057c, _, _⟩
          linarith only [hlam, hc125xy, htr012a, htr015b, htr057a, htr157a])
        obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd24b, hd78a, htr246a, htr346a, htr347a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd24b, hd79a, htr246a, htr346a, htr347a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
          linarith only [hlam, hd47a, hd56b, htr156a, htr157a, htr478a, htr578a])
        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc567yx, htr156a, htr157c, htr178a, htr578a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc124xy, hc478yz, htr012a, htr017a, htr146a, htr178a, htr346a, htr348a])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc045zy, htr058a, htr345a, htr348a, htr458c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd47a, hd56b, htr156a, htr157a, htr479a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc567yx, htr156a, htr157c, htr179a, htr579a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd45a, hd89b, htr057a, htr058a, htr457a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd45a, hd58b, htr345a, htr348a, htr489a, htr589a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        rcases m.htr 6 8 9 (by decide) (by decide) with
          ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
        ·
          linarith only [hlam, hc124xy, hc678yz, htr012a, htr017a, htr146a, htr178a, htr468c, htr489a, htr689a]
        ·
          linarith only [hlam, hc123xy, hc789zy, htr012a, htr013c, htr017a, htr036a, htr179a, htr368a, htr689a]
  ·
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr345c, htr347b, htr357c])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr367a, htr367b, htr367c, _, _⟩
        linarith only [hlam, htr346c, htr347b, htr367c])
      obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
      have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr457a, htr457b, htr457c, _, _⟩
        linarith only [hlam, htr345b, htr357a, htr457a])
      obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc145zy, htr157a, htr345a, htr347a, htr457c])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr456a, htr456b, htr456c, _, _⟩
        linarith only [hlam, hc567xy, htr345a, htr347a, htr456a, htr457c])
      obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
      have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr458a, htr458b, htr458c, _, _⟩
        linarith only [hlam, hc578yx, htr345a, htr347a, htr457c, htr458a])
      obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
      have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr467a, htr467b, htr467c, _, _⟩
        linarith only [hlam, htr346b, htr367a, htr467a])
      obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc146zy, htr167a, htr346a, htr347a, htr467c])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc678yx, htr346a, htr347a, htr467c, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc679yx, htr346a, htr347a, htr467c, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
        linarith only [hlam, hc456yz, htr346a, htr347a, htr467c, htr567a])
      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
      have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr156a, htr156b, htr156c, _, _⟩
        linarith only [hlam, hd12a, hd67b, htr012a, htr015a, htr156a, htr567a])
      obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
      have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr056a, htr056b, htr056c, _, _⟩
        linarith only [hlam, hc125xy, htr012a, htr015b, htr056a, htr156a])
      obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc457xy, htr045c, htr047a, htr056a, htr456a])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, hc458xy, htr047a, htr048a, htr345a, htr347a])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hd46a, hd57b, htr156a, htr157a, htr468a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr167a, htr168a, htr456a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc124xy, hc468yz, htr012a, htr014c, htr016a, htr047a, htr168a, htr347a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc045zy, htr058a, htr345a, htr348a, htr458c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hd46a, hd57b, htr156a, htr157a, htr469a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hd45a, hd67b, htr167a, htr169a, htr456a, htr569a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr012a, htr015a, htr157a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd45a, hd57b, htr345a, htr347a, htr478a, htr578a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd45a, hd89b, htr056a, htr058a, htr456a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd45a, hd58b, htr345a, htr348a, htr489a, htr589a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc124xy, hc678zy, htr012a, htr014c, htr016a, htr048a, htr168a, htr489a, htr789a]
      ·
        linarith only [hlam, hc124xy, hc689zy, htr012a, htr014c, htr016a, htr047a, htr169a, htr478a, htr789a]
    ·
      rcases m.htr 3 4 8 (by decide) (by decide) with
        ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, htr345c, htr348b, htr358c])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, htr346c, htr348b, htr368c])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr458a, htr458b, htr458c, _, _⟩
          linarith only [hlam, htr345b, htr358a, htr458a])
        obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, hc145zy, htr158a, htr345a, htr348a, htr458c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr456a, htr456b, htr456c, _, _⟩
          linarith only [hlam, hc568xy, htr345a, htr348a, htr456a, htr458c])
        obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr346b, htr368a, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc146zy, htr168a, htr346a, htr348a, htr468c])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc678xy, htr346a, htr348a, htr467a, htr468c])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hc456yz, htr346a, htr348a, htr468c, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr156a, htr156b, htr156c, _, _⟩
          linarith only [hlam, hd12a, hd68b, htr012a, htr015a, htr156a, htr568a])
        obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
        have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr056a, htr056b, htr056c, _, _⟩
          linarith only [hlam, hc125xy, htr012a, htr015b, htr056a, htr156a])
        obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc458xy, htr045c, htr048a, htr056a, htr456a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
          linarith only [hlam, hc124xy, hc467yz, htr012a, htr014c, htr016a, htr048a, htr167a, htr347a, htr348a])
        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
        rcases m.htr 5 6 7 (by decide) (by decide) with
          ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
        ·
          linarith only [hlam, hd45a, hd68b, htr167a, htr168a, htr456a, htr567a]
        ·
          linarith only [hlam, hd46a, hd58b, htr156a, htr158a, htr467a, htr567a]
      ·
        rcases m.htr 3 4 9 (by decide) (by decide) with
          ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
        ·
          have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr359a, htr359b, htr359c, _, _⟩
            linarith only [hlam, htr345c, htr349b, htr359c])
          obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, htr346c, htr349b, htr369c])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, htr345b, htr359a, htr459a])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr159a, htr159b, htr159c, _, _⟩
            linarith only [hlam, hc145zy, htr159a, htr345a, htr349a, htr459c])
          obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
          have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr456a, htr456b, htr456c, _, _⟩
            linarith only [hlam, hc569xy, htr345a, htr349a, htr456a, htr459c])
          obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, htr346b, htr369a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr169a, htr169b, htr169c, _, _⟩
            linarith only [hlam, hc146zy, htr169a, htr346a, htr349a, htr469c])
          obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc679xy, htr346a, htr349a, htr467a, htr469c])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr569a, htr569b, htr569c, _, _⟩
            linarith only [hlam, hc456yz, htr346a, htr349a, htr469c, htr569a])
          obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
          have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr156a, htr156b, htr156c, _, _⟩
            linarith only [hlam, hd12a, hd69b, htr012a, htr015a, htr156a, htr569a])
          obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
          have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr056a, htr056b, htr056c, _, _⟩
            linarith only [hlam, hc125xy, htr012a, htr015b, htr056a, htr156a])
          obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
          have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr049a, htr049b, htr049c, _, _⟩
            linarith only [hlam, hc459xy, htr045c, htr049a, htr056a, htr456a])
          obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc124xy, hc467yz, htr012a, htr014c, htr016a, htr049a, htr167a, htr347a, htr349a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 5 6 7 (by decide) (by decide) with
            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
          ·
            linarith only [hlam, hd45a, hd69b, htr167a, htr169a, htr456a, htr567a]
          ·
            linarith only [hlam, hd46a, hd59b, htr156a, htr159a, htr467a, htr567a]
        ·
          rcases m.htr 3 4 10 (by decide) (by decide) with
            ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
          ·
            have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
              linarith only [hlam, htr3410b, htr345c, htr3510c])
            obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
            have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
              linarith only [hlam, htr3410b, htr346c, htr3610c])
            obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
            have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
              linarith only [hlam, htr345b, htr3510a, htr4510a])
            obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
            have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
              linarith only [hlam, hc145zy, htr1510a, htr3410a, htr345a, htr4510c])
            obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
            have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr456a, htr456b, htr456c, _, _⟩
              linarith only [hlam, hc5610xy, htr3410a, htr345a, htr4510c, htr456a])
            obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
            have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
              linarith only [hlam, htr346b, htr3610a, htr4610a])
            obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
            have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
              linarith only [hlam, hc146zy, htr1610a, htr3410a, htr346a, htr4610c])
            obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc6710xy, htr3410a, htr346a, htr4610c, htr467a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              linarith only [hlam, hc456yz, htr3410a, htr346a, htr4610c, htr5610a])
            obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
            have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr156a, htr156b, htr156c, _, _⟩
              linarith only [hlam, hd12a, hd610b, htr012a, htr015a, htr156a, htr5610a])
            obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
            have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr056a, htr056b, htr056c, _, _⟩
              linarith only [hlam, hc125xy, htr012a, htr015b, htr056a, htr156a])
            obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
            have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
              linarith only [hlam, hc4510xy, htr0410a, htr045c, htr056a, htr456a])
            obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
              linarith only [hlam, hc124xy, hc467yz, htr012a, htr014c, htr016a, htr0410a, htr167a, htr3410a, htr347a])
            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
            rcases m.htr 5 6 7 (by decide) (by decide) with
              ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
            ·
              linarith only [hlam, hd45a, hd610b, htr1610a, htr167a, htr456a, htr567a]
            ·
              linarith only [hlam, hd46a, hd510b, htr1510a, htr156a, htr467a, htr567a]
          ·
            rcases m.htr 4 5 6 (by decide) (by decide) with
              ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
            ·
              rcases m.htr 2 5 6 (by decide) (by decide) with
                ⟨htr256a, htr256b, htr256c, _, _⟩ | ⟨htr256a, htr256b, htr256c, _, _⟩
              ·
                have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                  linarith only [hlam, hc123xy, hc567yx, htr012a, htr015a, htr125c, htr134a, htr256a, htr345a, htr457a])
                obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd12a, hd67b, htr012a, htr015a, htr125c, htr256a, htr567a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                  linarith only [hlam, hd12a, hd68b, htr012a, htr015a, htr125c, htr256a, htr568a])
                obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr168a, htr568a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                rcases m.htr 4 6 7 (by decide) (by decide) with
                  ⟨htr467a, htr467b, htr467c, _, _⟩ | ⟨htr467a, htr467b, htr467c, _, _⟩
                ·
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hc456yz, htr125c, htr157a, htr256a, htr467a, htr567b])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd12a, hd78b, htr012a, htr015a, htr157a, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hd12a, hd79b, htr012a, htr015a, htr157a, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr578a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                    linarith only [hlam, hc456yz, htr467b, htr478a, htr567a, htr678a])
                  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                    linarith only [hlam, hc123xy, hc578zy, htr012a, htr015a, htr134a, htr158a, htr347a, htr478a])
                  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
                  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                    linarith only [hlam, hc456yz, htr467a, htr567c, htr579a, htr679a])
                  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                    linarith only [hlam, hc456yz, htr467b, htr479a, htr567a, htr679a])
                  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                    linarith only [hlam, hc123xy, hc789yz, htr012a, htr018a, htr134a, htr189a, htr347a, htr479a])
                  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hc568yx, htr125c, htr158c, htr189a, htr256a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 7 8 9 (by decide) (by decide) with
                    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                  ·
                    linarith only [hlam, hd56b, hd78a, htr125c, htr158a, htr256a, htr589a, htr789a]
                  ·
                    linarith only [hlam, hd23b, hd89a, htr234a, htr347a, htr478a, htr789a]
                ·
                  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                    linarith only [hlam, hc123xy, hc567zy, htr012a, htr015a, htr134a, htr157a, htr346a, htr467a])
                  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                    linarith only [hlam, hc125xy, htr012a, htr015b, htr057a, htr157a])
                  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd23b, hd78a, htr234a, htr346a, htr467a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hd56b, hd67a, htr125c, htr157a, htr256a, htr578a, htr678a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                    linarith only [hlam, hc567yx, htr125c, htr157c, htr178a, htr256a, htr578a])
                  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                    linarith only [hlam, hc123xy, hc678yz, htr012a, htr017a, htr134a, htr178a, htr346a, htr468a])
                  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                    linarith only [hlam, hc456yz, htr025c, htr058a, htr256a, htr468a, htr568b])
                  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                    linarith only [hlam, hc789yx, htr057a, htr058a, htr578c, htr579a])
                  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                    linarith only [hlam, hc567yx, htr125c, htr157c, htr179a, htr256a, htr579a])
                  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                  have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                    linarith only [hlam, hc123xy, hc789zy, htr012a, htr017a, htr134a, htr179a, htr348a, htr489a])
                  obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                    linarith only [hlam, hd45a, hd89b, htr057a, htr058a, htr457a, htr589a])
                  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                  rcases m.htr 6 8 9 (by decide) (by decide) with
                    ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                  ·
                    linarith only [hlam, hc456yz, htr468a, htr568c, htr589a, htr689a]
                  ·
                    linarith only [hlam, hc126xy, hc478yz, htr012a, htr017a, htr168a, htr178a, htr489a, htr689a]
              ·
                have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr156a, htr156b, htr156c, _, _⟩
                  linarith only [hlam, hd12a, hd25b, htr012a, htr015a, htr156a, htr256a])
                obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
                have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr056a, htr056b, htr056c, _, _⟩
                  linarith only [hlam, hc125xy, htr012a, htr015b, htr056a, htr156a])
                obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
                rcases m.htr 3 5 6 (by decide) (by decide) with
                  ⟨htr356a, htr356b, htr356c, _, _⟩ | ⟨htr356a, htr356b, htr356c, _, _⟩
                ·
                  rcases m.htr 5 6 7 (by decide) (by decide) with
                    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                  ·
                    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                      linarith only [hlam, hc245zy, htr126c, htr167a, htr256c, htr456a, htr567a])
                    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc123xy, hc678yx, htr012a, htr016a, htr134a, htr167a, htr346a, htr468a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                      linarith only [hlam, hc123xy, hc679yx, htr012a, htr016a, htr134a, htr167a, htr346a, htr469a])
                    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc245zy, htr256a, htr456b, htr468a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc245zy, htr126c, htr168a, htr256c, htr456a, htr568a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc123xy, hc678zy, htr012a, htr016a, htr134a, htr168a, htr347a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc245zy, htr256a, htr456b, htr469a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                      linarith only [hlam, hc245zy, htr126c, htr169a, htr256c, htr456a, htr569a])
                    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                      linarith only [hlam, hc123xy, hc689zy, htr012a, htr016a, htr134a, htr169a, htr348a, htr489a])
                    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd12a, hd89b, htr012a, htr016a, htr168a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a]
                    ·
                      linarith only [hlam, hc467yz, htr478b, htr489a, htr678a, htr789a]
                  ·
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc245zy, htr256a, htr456b, htr467a, htr567a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc123xy, hc678xy, htr012a, htr016a, htr134a, htr168a, htr346a, htr467a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                      linarith only [hlam, hc123xy, hc679xy, htr012a, htr016a, htr134a, htr169a, htr346a, htr467a])
                    obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc245zy, htr126c, htr168a, htr256c, htr456a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                      linarith only [hlam, hc245zy, htr256a, htr456b, htr468a, htr568a])
                    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                      linarith only [hlam, hc123xy, hc678yz, htr012a, htr017a, htr134a, htr178a, htr346a, htr468a])
                    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                    have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                      linarith only [hlam, hc245zy, htr126c, htr169a, htr256c, htr456a, htr569a])
                    obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                    have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                      linarith only [hlam, hc245zy, htr256a, htr456b, htr469a, htr569a])
                    obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc123xy, hc689yz, htr012a, htr018a, htr134a, htr189a, htr346a, htr469a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                      linarith only [hlam, hd23b, hd78a, htr234a, htr346a, htr467a, htr678a])
                    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                      linarith only [hlam, hd23b, hd89a, htr234a, htr346a, htr468a, htr689a])
                    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                    rcases m.htr 7 8 9 (by decide) (by decide) with
                      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                    ·
                      linarith only [hlam, hc167zy, htr178c, htr189a, htr678a, htr789a]
                    ·
                      linarith only [hlam, hc167zy, htr178a, htr678b, htr689a, htr789a]
                ·
                  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
                    linarith only [hlam, hd23b, hd57a, htr235a, htr356a, htr456a, htr457a])
                  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
                  rcases m.htr 3 5 7 (by decide) (by decide) with
                    ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, hc045zy, htr057a, htr356a, htr357a, htr456a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                      linarith only [hlam, htr056c, htr057b, htr067c])
                    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                      linarith only [hlam, hc145zy, htr157a, htr356a, htr357a, htr456a])
                    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                      linarith only [hlam, hc126xy, htr012a, htr016b, htr067a, htr167a])
                    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                    have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                      linarith only [hlam, hc123xy, hc678yx, htr012a, htr016a, htr135a, htr167a, htr356a, htr568a])
                    obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                    have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                      linarith only [hlam, hc245zy, htr126c, htr168a, htr256c, htr456a, htr568a])
                    obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                      linarith only [hlam, hc123xy, hc678zy, htr012a, htr016a, htr134a, htr168a, htr347a, htr478a])
                    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                    have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                      linarith only [hlam, hc123xy, hc457yz, htr012a, htr015a, htr134a, htr157a, htr347c, htr378a, htr478a])
                    obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                    rcases m.htr 6 7 8 (by decide) (by decide) with
                      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                    ·
                      linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a]
                    ·
                      linarith only [hlam, hd45a, hd67b, htr356a, htr357b, htr378a, htr456a, htr678a]
                  ·
                    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
                      linarith only [hlam, htr035b, htr057a, htr357a])
                    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
                    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                      linarith only [hlam, hc123xy, htr012a, htr015a, htr135a, htr157a, htr357a])
                    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
                    rcases m.htr 3 5 8 (by decide) (by decide) with
                      ⟨htr358a, htr358b, htr358c, _, _⟩ | ⟨htr358a, htr358b, htr358c, _, _⟩
                    ·
                      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
                        linarith only [hlam, hc045zy, htr058a, htr356a, htr358a, htr456a])
                      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
                      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                        linarith only [hlam, htr056c, htr058b, htr068c])
                      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, htr057c, htr058b, htr078c])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                        linarith only [hlam, hc126xy, htr012a, htr016b, htr068a, htr168a])
                      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                        linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a])
                      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                      have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                        linarith only [hlam, hc123xy, hc678xy, htr012a, htr016a, htr135a, htr168a, htr356a, htr567a])
                      obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                        linarith only [hlam, hc245zy, htr126c, htr167a, htr256c, htr456a, htr567a])
                      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                      rcases m.htr 6 7 8 (by decide) (by decide) with
                        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                      ·
                        linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a]
                      ·
                        linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a]
                    ·
                      rcases m.htr 3 5 9 (by decide) (by decide) with
                        ⟨htr359a, htr359b, htr359c, _, _⟩ | ⟨htr359a, htr359b, htr359c, _, _⟩
                      ·
                        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                          linarith only [hlam, hc045zy, htr059a, htr356a, htr359a, htr456a])
                        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
                        have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                          linarith only [hlam, htr056c, htr059b, htr069c])
                        obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, htr057c, htr059b, htr079c])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                          linarith only [hlam, hc126xy, htr012a, htr016b, htr069a, htr169a])
                        obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc127xy, htr012a, htr017b, htr079a, htr179a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                          linarith only [hlam, hc123xy, hc679xy, htr012a, htr016a, htr135a, htr169a, htr356a, htr567a])
                        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                        have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                          linarith only [hlam, hc245zy, htr126c, htr167a, htr256c, htr456a, htr567a])
                        obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                        rcases m.htr 6 7 9 (by decide) (by decide) with
                          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                        ·
                          linarith only [hlam, hd12a, hd79b, htr012a, htr016a, htr167a, htr679a]
                        ·
                          linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr179a, htr679a]
                      ·
                        rcases m.htr 3 5 10 (by decide) (by decide) with
                          ⟨htr3510a, htr3510b, htr3510c, _, _⟩ | ⟨htr3510a, htr3510b, htr3510c, _, _⟩
                        ·
                          have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                            linarith only [hlam, hc045zy, htr0510a, htr3510a, htr356a, htr456a])
                          obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                          have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                            linarith only [hlam, htr0510b, htr056c, htr0610c])
                          obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                            linarith only [hlam, htr0510b, htr057c, htr0710c])
                          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                          have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                            linarith only [hlam, hc126xy, htr012a, htr016b, htr0610a, htr1610a])
                          obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
                          have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                            linarith only [hlam, hc127xy, htr012a, htr017b, htr0710a, htr1710a])
                          obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                          have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                            linarith only [hlam, hc123xy, hc6710xy, htr012a, htr016a, htr135a, htr1610a, htr356a, htr567a])
                          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                            linarith only [hlam, hc245zy, htr126c, htr167a, htr256c, htr456a, htr567a])
                          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                          rcases m.htr 6 7 10 (by decide) (by decide) with
                            ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                          ·
                            linarith only [hlam, hd12a, hd710b, htr012a, htr016a, htr167a, htr6710a]
                          ·
                            linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr1710a, htr6710a]
                        ·
                          rcases m.htr 5 6 7 (by decide) (by decide) with
                            ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                          ·
                            have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                              linarith only [hlam, hc245zy, htr126c, htr167a, htr256c, htr456a, htr567a])
                            obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                              linarith only [hlam, hc123xy, hc678yx, htr012a, htr016a, htr135a, htr167a, htr356a, htr568a])
                            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                              linarith only [hlam, hc245zy, htr126c, htr168a, htr256c, htr456a, htr568a])
                            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                              linarith only [hlam, hc123xy, hc678zy, htr012a, htr016a, htr134a, htr168a, htr347a, htr478a])
                            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                              linarith only [hlam, hc123xy, hc467yz, htr012a, htr016a, htr134a, htr167a, htr347c, htr378a, htr478a])
                            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc145zy, htr157c, htr178a, htr357b, htr378a, htr457a])
                            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a]
                            ·
                              linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a]
                          ·
                            have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                              linarith only [hlam, hc123xy, hc678xy, htr012a, htr016a, htr135a, htr168a, htr356a, htr567a])
                            obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                              linarith only [hlam, hc245zy, htr126c, htr168a, htr256c, htr356b, htr368a, htr456a])
                            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                              linarith only [hlam, hc245zy, htr256a, htr456b, htr467a, htr567a])
                            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                              linarith only [hlam, hd23b, hd67a, htr234a, htr346c, htr368a, htr467a, htr468a])
                            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc123xy, hc678yz, htr012a, htr017a, htr134a, htr178a, htr346a, htr468a])
                            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                              linarith only [hlam, hc145zy, htr157c, htr178a, htr457a, htr578a])
                            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                            rcases m.htr 6 7 8 (by decide) (by decide) with
                              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                            ·
                              linarith only [hlam, hd23b, hd67a, htr235a, htr357a, htr578a, htr678a]
                            ·
                              linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a]
            ·
              have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr157a, htr157b, htr157c, _, _⟩
                linarith only [hlam, hc123xy, hc567xy, htr012a, htr015a, htr134a, htr157a, htr345a, htr456a])
              obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
              have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr158a, htr158b, htr158c, _, _⟩
                linarith only [hlam, hc123xy, hc568xy, htr012a, htr015a, htr134a, htr158a, htr345a, htr456a])
              obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
              have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                linarith only [hlam, hd23b, hd67a, htr234a, htr345a, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                linarith only [hlam, hd23b, hd68a, htr234a, htr345a, htr456a, htr568a])
              obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
              rcases m.htr 4 5 7 (by decide) (by decide) with
                ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc156zy, htr167a, htr456a, htr457a, htr567c])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr357a, htr357b, htr357c, _, _⟩
                  linarith only [hlam, hd23b, hd56a, htr235a, htr357a, htr456a, htr457a])
                obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd56a, hd67b, htr456a, htr457a, htr578a, htr678a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                  linarith only [hlam, hc567xy, htr456a, htr457b, htr478a, htr578a])
                obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                  linarith only [hlam, hc123xy, hc678zy, htr012a, htr016a, htr134a, htr168a, htr347a, htr478a])
                obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc123xy, hc789xy, htr012a, htr017a, htr134a, htr179a, htr347a, htr478a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr358a, htr358b, htr358c, _, _⟩
                  linarith only [hlam, hc156zy, htr168a, htr345b, htr358a, htr456a, htr568c])
                obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd17b, hd56a, htr179a, htr456a, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, hc567xy, htr456a, htr457b, htr479a, htr579a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc123xy, hc789yz, htr012a, htr018a, htr134a, htr189a, htr347a, htr479a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hd15b, hd89a, htr157a, htr357a, htr358a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 6 8 9 (by decide) (by decide) with
                  ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
                ·
                  linarith only [hlam, hc156zy, htr168c, htr189a, htr568a, htr689a]
                ·
                  linarith only [hlam, hc156zy, htr168a, htr568b, htr589a, htr689a]
              ·
                have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                  linarith only [hlam, hc123xy, hc567yz, htr012a, htr016a, htr134a, htr167a, htr345a, htr457a])
                obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                  linarith only [hlam, hd23b, hd78a, htr234a, htr345a, htr457a, htr578a])
                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                  linarith only [hlam, hd23b, hd79a, htr234a, htr345a, htr457a, htr579a])
                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                  linarith only [hlam, hc156zy, htr167a, htr567b, htr578a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc156zy, htr167c, htr178a, htr567a, htr678a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr458a, htr458b, htr458c, _, _⟩
                  linarith only [hlam, hc123xy, hc578yz, htr012a, htr017a, htr134a, htr178a, htr345a, htr458a])
                obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                  linarith only [hlam, hc156zy, htr167a, htr567b, htr579a, htr679a])
                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                  linarith only [hlam, hc156zy, htr167c, htr179a, htr567a, htr679a])
                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                  linarith only [hlam, hc123xy, hc789zy, htr012a, htr017a, htr134a, htr179a, htr348a, htr489a])
                obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                  linarith only [hlam, hc125xy, hc478yz, htr012a, htr017a, htr158a, htr178a, htr489a, htr589a])
                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                rcases m.htr 7 8 9 (by decide) (by decide) with
                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                ·
                  linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
                ·
                  linarith only [hlam, hd56a, hd78b, htr456a, htr458a, htr589a, htr789a]

theorem shard_317 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    : False :=
  proof_shard_317 m htr012a htr013c htr014a htr014c htr015a htr015b htr016a htr016b htr017a htr017b htr018a htr025c htr034a htr035b htr045c htr124c htr125c htr126c htr134a htr135a htr234a htr235a htr245c htr345a htr345b htr345c

#print axioms shard_317
end Jsp404.NoSatElevenDBMTerminal
