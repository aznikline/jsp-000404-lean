import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_316 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr037a : m.d 3 7 + lam ≤ m.d 0 3)
    (htr038a : m.d 3 8 + lam ≤ m.d 0 3)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < 4*lam := by
    linarith only [hd03braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd17a, hd17braw⟩ := m.hrange 1 7 (by decide)
  have hd17b : m.d 1 7 < 4*lam := by
    linarith only [hd17braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  have hd46a := (m.hrange 4 6 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd610a := (m.hrange 6 10 (by decide)).1
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
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc146xy, hc146yx, hc146yz, hc146zy⟩ := endpoint_caps m 1 4 6 (by decide) (by decide)
  obtain ⟨hc147xy, hc147yx, hc147yz, hc147zy⟩ := endpoint_caps m 1 4 7 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
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
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr045a, htr046a, htr456c])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr045b, htr056a, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, htr014c, htr045a, htr146a, htr456c])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc124xy, htr012a, htr015a, htr145a, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr124c, htr145a, htr246a, htr456c])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc234zy, htr245a, htr345b, htr356a, htr456a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr047a, htr047b, htr047c, _, _⟩
        linarith only [hlam, hc567xy, htr045a, htr047a, htr456a, htr457c])
      obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc234zy, htr025c, htr057a, htr245c, htr345a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr067a, htr067b, htr067c, _, _⟩
        linarith only [hlam, htr056c, htr057b, htr067c])
      obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
      have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr157a, htr157b, htr157c, _, _⟩
        linarith only [hlam, hc234zy, htr125c, htr157a, htr245c, htr345a, htr457a])
      obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc126xy, htr012a, htr016b, htr067a, htr167a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr357a, htr357b, htr357c, _, _⟩
        linarith only [hlam, htr345c, htr357a, htr457a])
      obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc124xy, hc678yx, htr012a, htr016a, htr145a, htr167a, htr456a, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr068a, htr068b, htr068c, _, _⟩
        linarith only [hlam, hc567xy, htr056c, htr057a, htr068a, htr568a])
      obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc567xy, htr156c, htr157a, htr168a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc468yz, htr046b, htr068a, htr346a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc124xy, hc679yx, htr012a, htr016a, htr145a, htr167a, htr456a, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc567xy, htr156c, htr157a, htr169a, htr569a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr012a, htr015a, htr157a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hc567xy, htr047b, htr078a, htr456a, htr457b, htr578a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr048a, htr048b, htr048c, _, _⟩
        linarith only [hlam, htr047c, htr048b, htr078c])
      obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
      have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr148a, htr148b, htr148c, _, _⟩
        linarith only [hlam, htr014c, htr048a, htr148a])
      obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, hc567xy, htr356a, htr357b, htr378a, htr578a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12a, hd89b, htr012a, htr016a, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr012a, htr018a, htr189a, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc134zy, htr148c, htr189a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hc124xy, hc678zy, htr012a, htr014c, htr016a, htr048a, htr168a, htr489a, htr789a]
      ·
        linarith only [hlam, hc123xy, hc689zy, htr012a, htr013c, htr016a, htr037a, htr169a, htr378a, htr789a]
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, htr045b, htr057a, htr457a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr147a, htr147b, htr147c, _, _⟩
        linarith only [hlam, htr014c, htr045a, htr147a, htr457c])
      obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
      rcases m.htr 3 4 7 (by decide) (by decide) with
        ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
      ·
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr058a, htr058b, htr058c, _, _⟩
            linarith only [hlam, hc234zy, htr025c, htr058a, htr245c, htr345a, htr458a])
          obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
            linarith only [hlam, htr056c, htr058b, htr068c])
          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
            linarith only [hlam, htr057c, htr058b, htr078c])
          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
          have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr158a, htr158b, htr158c, _, _⟩
            linarith only [hlam, hc234zy, htr125c, htr158a, htr245c, htr345a, htr458a])
          obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
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
            linarith only [hlam, hc124xy, hc678xy, htr012a, htr016a, htr145a, htr168a, htr456a, htr567a])
          obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
          have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr167a, htr167b, htr167c, _, _⟩
            linarith only [hlam, hc568xy, htr156c, htr158a, htr167a, htr567a])
          obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a]
          ·
            linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a]
        ·
          rcases m.htr 3 4 8 (by decide) (by decide) with
            ⟨htr348a, htr348b, htr348c, _, _⟩ | ⟨htr348a, htr348b, htr348c, _, _⟩
          ·
            rcases m.htr 4 5 9 (by decide) (by decide) with
              ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
            ·
              have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr059a, htr059b, htr059c, _, _⟩
                linarith only [hlam, hc234zy, htr025c, htr059a, htr245c, htr345a, htr459a])
              obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, htr056c, htr059b, htr069c])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                linarith only [hlam, htr057c, htr059b, htr079c])
              obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
              have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr159a, htr159b, htr159c, _, _⟩
                linarith only [hlam, hc234zy, htr125c, htr159a, htr245c, htr345a, htr459a])
              obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
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
                linarith only [hlam, hc124xy, hc679xy, htr012a, htr016a, htr145a, htr169a, htr456a, htr567a])
              obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
              have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                linarith only [hlam, hc569xy, htr156c, htr159a, htr167a, htr567a])
              obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
              rcases m.htr 6 7 9 (by decide) (by decide) with
                ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd79b, htr012a, htr016a, htr167a, htr679a]
              ·
                linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr179a, htr679a]
            ·
              rcases m.htr 3 4 9 (by decide) (by decide) with
                ⟨htr349a, htr349b, htr349c, _, _⟩ | ⟨htr349a, htr349b, htr349c, _, _⟩
              ·
                rcases m.htr 4 5 10 (by decide) (by decide) with
                  ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                ·
                  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
                    linarith only [hlam, hc234zy, htr025c, htr0510a, htr245c, htr345a, htr4510a])
                  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
                  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                    linarith only [hlam, htr0510b, htr056c, htr0610c])
                  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                    linarith only [hlam, htr0510b, htr057c, htr0710c])
                  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
                    linarith only [hlam, hc234zy, htr125c, htr1510a, htr245c, htr345a, htr4510a])
                  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
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
                    linarith only [hlam, hc124xy, hc6710xy, htr012a, htr016a, htr145a, htr1610a, htr456a, htr567a])
                  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
                    linarith only [hlam, hc5610xy, htr1510a, htr156c, htr167a, htr567a])
                  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
                  rcases m.htr 6 7 10 (by decide) (by decide) with
                    ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                  ·
                    linarith only [hlam, hd12a, hd710b, htr012a, htr016a, htr167a, htr6710a]
                  ·
                    linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr1710a, htr6710a]
                ·
                  rcases m.htr 3 4 10 (by decide) (by decide) with
                    ⟨htr3410a, htr3410b, htr3410c, _, _⟩ | ⟨htr3410a, htr3410b, htr3410c, _, _⟩
                  ·
                    rcases m.htr 5 6 7 (by decide) (by decide) with
                      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
                    ·
                      rcases m.htr 2 6 7 (by decide) (by decide) with
                        ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
                      ·
                        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                          linarith only [hlam, hc123xy, htr012a, htr013c, htr016a, htr036a, htr126c, htr267a, htr367a])
                        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                        have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                          linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr126c, htr267a, htr678a])
                        obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                          linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a])
                        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                          linarith only [hlam, hc134zy, htr147c, htr178a, htr347a, htr478a])
                        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                        have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                          linarith only [hlam, hc124xy, hc567yz, htr012a, htr016a, htr126c, htr145a, htr267a, htr457c, htr478a, htr578a])
                        obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                          linarith only [hlam, hc124xy, hc678zy, htr012a, htr016a, htr145a, htr168a, htr457a, htr578a])
                        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc124xy, hc789xy, htr012a, htr017a, htr145a, htr179a, htr457a, htr578a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                          linarith only [hlam, hc134zy, htr146c, htr168a, htr346a, htr468a])
                        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                          linarith only [hlam, hc234zy, htr245a, htr346b, htr368a, htr456c, htr468a])
                        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                        have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                          linarith only [hlam, hc127xy, hc678yx, htr012a, htr016a, htr126c, htr179a, htr267a, htr367b, htr368a, htr379a])
                        obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                          linarith only [hlam, hc123xy, hc567yz, htr012a, htr013c, htr016a, htr037a, htr126c, htr267a, htr379a, htr579a])
                        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc124xy, hc789yz, htr012a, htr018a, htr145a, htr189a, htr457a, htr579a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                          linarith only [hlam, hc678yx, htr126c, htr168c, htr189a, htr267a, htr689a])
                        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                        rcases m.htr 7 8 9 (by decide) (by decide) with
                          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                        ·
                          linarith only [hlam, hd67b, hd78a, htr126c, htr168a, htr267a, htr689a, htr789a]
                        ·
                          linarith only [hlam, hd24b, hd89a, htr245a, htr457a, htr578a, htr789a]
                      ·
                        have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr067a, htr067b, htr067c, _, _⟩
                          linarith only [hlam, hc234zy, htr046b, htr067a, htr246c, htr267a, htr346a])
                        obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
                        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                          linarith only [hlam, hc234zy, htr246c, htr267a, htr346a, htr467a])
                        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                          linarith only [hlam, hc234zy, htr245a, htr346b, htr367a, htr456c, htr467a])
                        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
                        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                          linarith only [hlam, hd24b, hd68a, htr245a, htr456c, htr467a, htr567a, htr568a])
                        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                        rcases m.htr 4 6 8 (by decide) (by decide) with
                          ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
                        ·
                          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                            linarith only [hlam, hc056zy, htr068a, htr467a, htr468a, htr567a])
                          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                          have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                            linarith only [hlam, htr067c, htr068b, htr078c])
                          obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                            linarith only [hlam, hc156zy, htr168a, htr467a, htr468a, htr567a])
                          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                            linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a])
                          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                            linarith only [hlam, htr346c, htr368a, htr468a])
                          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                            linarith only [hlam, hc124xy, hc789yx, htr012a, htr017a, htr145a, htr178a, htr456c, htr467a, htr679a])
                          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                            linarith only [hlam, hc256zy, htr127c, htr179a, htr267c, htr567a, htr679a])
                          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                            linarith only [hlam, hc124xy, hc789zy, htr012a, htr017a, htr145a, htr179a, htr458a, htr589a])
                          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                          have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                            linarith only [hlam, hc123xy, hc568yz, htr012a, htr013c, htr016a, htr038a, htr168a, htr389a, htr589a])
                          obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
                          ·
                            linarith only [hlam, hd56a, hd78b, htr367a, htr368b, htr389a, htr567a, htr789a]
                        ·
                          have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr068a, htr068b, htr068c, _, _⟩
                            linarith only [hlam, htr046b, htr068a, htr468a])
                          obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
                          have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                            linarith only [hlam, hc124xy, htr012a, htr016a, htr145a, htr168a, htr456c, htr468a])
                          obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
                            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
                            linarith only [hlam, hc456zy, htr367a, htr368a, htr468a, htr567a])
                          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
                          rcases m.htr 4 6 9 (by decide) (by decide) with
                            ⟨htr469a, htr469b, htr469c, _, _⟩ | ⟨htr469a, htr469b, htr469c, _, _⟩
                          ·
                            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                              linarith only [hlam, hc056zy, htr069a, htr467a, htr469a, htr567a])
                            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
                            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                              linarith only [hlam, htr067c, htr069b, htr079c])
                            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                              linarith only [hlam, htr068c, htr069b, htr089c])
                            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                            have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                              linarith only [hlam, hc127xy, htr012a, htr017b, htr079a, htr179a])
                            obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                              linarith only [hlam, hc128xy, htr012a, htr018b, htr089a, htr189a])
                            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                            have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                              linarith only [hlam, hc124xy, hc789xy, htr012a, htr017a, htr145a, htr179a, htr456c, htr467a, htr678a])
                            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                              linarith only [hlam, hc256zy, htr127c, htr178a, htr267c, htr567a, htr678a])
                            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                            rcases m.htr 7 8 9 (by decide) (by decide) with
                              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                            ·
                              linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
                            ·
                              linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
                          ·
                            rcases m.htr 4 6 10 (by decide) (by decide) with
                              ⟨htr4610a, htr4610b, htr4610c, _, _⟩ | ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                            ·
                              have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                                linarith only [hlam, hc056zy, htr0610a, htr4610a, htr467a, htr567a])
                              obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                              have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                                linarith only [hlam, htr0610b, htr067c, htr0710c])
                              obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                              have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                                linarith only [hlam, htr0610b, htr068c, htr0810c])
                              obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                              have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                                linarith only [hlam, hc127xy, htr012a, htr017b, htr0710a, htr1710a])
                              obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                                linarith only [hlam, hc128xy, htr012a, htr018b, htr0810a, htr1810a])
                              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                                linarith only [hlam, hc124xy, hc7810xy, htr012a, htr017a, htr145a, htr1710a, htr456c, htr467a, htr678a])
                              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                                linarith only [hlam, hc256zy, htr127c, htr178a, htr267c, htr567a, htr678a])
                              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                              rcases m.htr 7 8 10 (by decide) (by decide) with
                                ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                              ·
                                linarith only [hlam, hd12a, hd810b, htr012a, htr017a, htr178a, htr7810a]
                              ·
                                linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr1810a, htr7810a]
                            ·
                              rcases m.htr 6 7 8 (by decide) (by decide) with
                                ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                              ·
                                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                                  linarith only [hlam, hc256zy, htr127c, htr178a, htr267c, htr567a, htr678a])
                                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                                have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                                  linarith only [hlam, hc124xy, hc789yx, htr012a, htr017a, htr145a, htr178a, htr456c, htr467a, htr679a])
                                obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                                  linarith only [hlam, hc256zy, htr127c, htr179a, htr267c, htr567a, htr679a])
                                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                                have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                                  linarith only [hlam, hc124xy, hc789zy, htr012a, htr017a, htr145a, htr179a, htr458a, htr589a])
                                obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                                have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr389a, htr389b, htr389c, _, _⟩
                                  linarith only [hlam, hc123xy, hc578yz, htr012a, htr013c, htr017a, htr038a, htr178a, htr389a, htr589a])
                                obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
                                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                                  linarith only [hlam, hc156zy, htr168c, htr189a, htr368b, htr389a, htr568a])
                                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                                rcases m.htr 7 8 9 (by decide) (by decide) with
                                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                                ·
                                  linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
                                ·
                                  linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
                              ·
                                have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                                  linarith only [hlam, hc124xy, hc789xy, htr012a, htr017a, htr145a, htr179a, htr456c, htr467a, htr678a])
                                obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                                  linarith only [hlam, hc256zy, htr127c, htr179a, htr267c, htr367b, htr379a, htr567a])
                                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                                have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                                  linarith only [hlam, hc256zy, htr267a, htr567b, htr578a, htr678a])
                                obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                                have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                                  linarith only [hlam, hd03b, hd78a, htr037a, htr379a, htr578a, htr579a])
                                obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                                  linarith only [hlam, hc124xy, hc789yz, htr012a, htr018a, htr145a, htr189a, htr457a, htr579a])
                                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                                  linarith only [hlam, hc156zy, htr168c, htr189a, htr568a, htr689a])
                                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                                rcases m.htr 7 8 9 (by decide) (by decide) with
                                  ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                                ·
                                  linarith only [hlam, hd24b, hd78a, htr245a, htr456c, htr468a, htr689a, htr789a]
                                ·
                                  linarith only [hlam, hd24b, hd89a, htr245a, htr456c, htr467a, htr678a, htr789a]
                    ·
                      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
                        linarith only [hlam, hc124xy, hc678xy, htr012a, htr016a, htr145a, htr168a, htr456a, htr567a])
                      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
                      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                        linarith only [hlam, hc124xy, hc679xy, htr012a, htr016a, htr145a, htr169a, htr456a, htr567a])
                      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
                      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
                        linarith only [hlam, hc134zy, htr146c, htr168a, htr346a, htr468a])
                      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
                      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                        linarith only [hlam, hc134zy, htr146c, htr169a, htr346a, htr469a])
                      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
                        linarith only [hlam, hd24b, hd67a, htr245a, htr456c, htr468a, htr567a, htr568a])
                      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
                      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                        linarith only [hlam, hc124xy, hc678yz, htr012a, htr017a, htr145a, htr178a, htr456a, htr568a])
                      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc134zy, htr147c, htr178a, htr347a, htr478a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                        linarith only [hlam, hd24b, hd67a, htr245a, htr456c, htr469a, htr567a, htr569a])
                      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                        linarith only [hlam, hc124xy, hc689yz, htr012a, htr018a, htr145a, htr189a, htr456a, htr569a])
                      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                        linarith only [hlam, hd24b, hd78a, htr245a, htr456a, htr567a, htr678a])
                      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hd24b, hd89a, htr245a, htr456a, htr568a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      rcases m.htr 7 8 9 (by decide) (by decide) with
                        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                      ·
                        linarith only [hlam, hc167zy, htr178c, htr189a, htr678a, htr789a]
                      ·
                        linarith only [hlam, hd24b, hd68a, htr245a, htr457c, htr478a, htr689a, htr789a]
                  ·
                    have hforced3610 := (m.htr 3 6 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3610a, htr3610b, htr3610c, _, _⟩
                      linarith only [hlam, htr3410c, htr346b, htr3610b])
                    obtain ⟨htr3610a, htr3610b, htr3610c, _, _⟩ := hforced3610
                    have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
                      linarith only [hlam, htr3410c, htr347b, htr3710b])
                    obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
                    have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
                      linarith only [hlam, htr346c, htr3610a, htr4610a])
                    obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
                    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                      linarith only [hlam, hc6710yx, htr3410a, htr346a, htr4610b, htr467a])
                    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                    have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                      linarith only [hlam, htr347c, htr3710a, htr4710a])
                    obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                    have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
                      linarith only [hlam, hd24b, hd56a, htr245a, htr3410a, htr345a, htr4610b, htr5610a])
                    obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
                    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                      linarith only [hlam, hd24b, hd610a, htr245a, htr456c, htr467a, htr5610a, htr567a])
                    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                    rcases m.htr 6 7 10 (by decide) (by decide) with
                      ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    ·
                      linarith only [hlam, hd24b, hd67a, htr245a, htr3410a, htr345a, htr4710b, htr6710a]
                    ·
                      linarith only [hlam, hd24b, hd710a, htr245a, htr456a, htr567a, htr6710a]
              ·
                have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr369a, htr369b, htr369c, _, _⟩
                  linarith only [hlam, htr346b, htr349c, htr369b])
                obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
                have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                  linarith only [hlam, htr347b, htr349c, htr379b])
                obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
                have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                  linarith only [hlam, htr346c, htr369a, htr469a])
                obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
                have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr467a, htr467b, htr467c, _, _⟩
                  linarith only [hlam, hc679yx, htr346a, htr349a, htr467a, htr469b])
                obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
                have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                  linarith only [hlam, htr347c, htr379a, htr479a])
                obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr569a, htr569b, htr569c, _, _⟩
                  linarith only [hlam, hd24b, hd56a, htr245a, htr345a, htr349a, htr469b, htr569a])
                obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
                have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
                  rintro ⟨htr567a, htr567b, htr567c, _, _⟩
                  linarith only [hlam, hd24b, hd69a, htr245a, htr456c, htr467a, htr567a, htr569a])
                obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
                rcases m.htr 6 7 9 (by decide) (by decide) with
                  ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
                ·
                  linarith only [hlam, hd24b, hd67a, htr245a, htr345a, htr349a, htr479b, htr679a]
                ·
                  linarith only [hlam, hd24b, hd79a, htr245a, htr456a, htr567a, htr679a]
          ·
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, htr346b, htr348c, htr368b])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, htr347b, htr348c, htr378b])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, htr346c, htr368a, htr468a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc678yx, htr346a, htr348a, htr467a, htr468b])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr478a, htr478b, htr478c, _, _⟩
              linarith only [hlam, htr347c, htr378a, htr478a])
            obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hd24b, hd56a, htr245a, htr345a, htr348a, htr468b, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr567a, htr567b, htr567c, _, _⟩
              linarith only [hlam, hd24b, hd68a, htr245a, htr456c, htr467a, htr567a, htr568a])
            obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
            rcases m.htr 6 7 8 (by decide) (by decide) with
              ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
            ·
              linarith only [hlam, hd24b, hd67a, htr245a, htr345a, htr348a, htr478b, htr678a]
            ·
              linarith only [hlam, hd24b, hd78a, htr245a, htr456a, htr567a, htr678a]
      ·
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, htr346b, htr347c, htr367b])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, htr346c, htr367a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, hc678xy, htr346a, htr347a, htr467b, htr468a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc679xy, htr346a, htr347a, htr467b, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hd24b, hd78a, htr245a, htr345a, htr347a, htr478a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr567a, htr567b, htr567c, _, _⟩
          linarith only [hlam, hd24b, hd56a, htr245a, htr345a, htr347a, htr467b, htr567a])
        obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
        have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr568a, htr568b, htr568c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr245a, htr456c, htr468a, htr567a, htr568a])
        obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc124xy, hc678yz, htr012a, htr017a, htr145a, htr178a, htr456a, htr568a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr348a, htr348b, htr348c, _, _⟩
          linarith only [hlam, hc147zy, htr178a, htr347a, htr348a, htr478c])
        obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd24b, hd89a, htr245a, htr345a, htr348a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr569a, htr569b, htr569c, _, _⟩
          linarith only [hlam, hd24b, hd67a, htr245a, htr456c, htr469a, htr567a, htr569a])
        obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc124xy, hc689yz, htr012a, htr018a, htr145a, htr189a, htr456a, htr569a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hc147zy, htr178c, htr189a, htr478a, htr789a]
        ·
          linarith only [hlam, hc147zy, htr178a, htr478b, htr489a, htr789a]
  ·
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc467xy, htr045a, htr047a, htr345a, htr346a])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr048a, htr048b, htr048c, _, _⟩
      linarith only [hlam, hc468xy, htr045a, htr048a, htr345a, htr346a])
    obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hc567xy, htr345a, htr346a, htr456b, htr457a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr458a, htr458b, htr458c, _, _⟩
      linarith only [hlam, hc568xy, htr345a, htr346a, htr456b, htr458a])
    obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd24b, hd67a, htr245a, htr345a, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hd24b, hd68a, htr245a, htr345a, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    rcases m.htr 3 4 7 (by decide) (by decide) with
      ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
    ·
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc146zy, htr167a, htr346a, htr347a, htr467c])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd46a, hd67b, htr346a, htr347a, htr478a, htr678a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc124xy, hc567yz, htr012a, htr014c, htr016a, htr047a, htr167a, htr478a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc124xy, hc678zy, htr012a, htr016a, htr145a, htr168a, htr457a, htr578a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc124xy, hc789xy, htr012a, htr017a, htr145a, htr179a, htr457a, htr578a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc146zy, htr168a, htr346a, htr348a, htr468c])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd17b, hd46a, htr179a, htr346a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hd24b, hd89a, htr245a, htr345a, htr348a, htr489a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc124xy, hc567yz, htr012a, htr014c, htr016a, htr047a, htr167a, htr479a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hc124xy, hc789yz, htr012a, htr018a, htr145a, htr189a, htr457a, htr579a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      rcases m.htr 6 8 9 (by decide) (by decide) with
        ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
      ·
        linarith only [hlam, hc146zy, htr168c, htr189a, htr468a, htr689a]
      ·
        linarith only [hlam, hc146zy, htr168a, htr468b, htr489a, htr689a]
    ·
      have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr167a, htr167b, htr167c, _, _⟩
        linarith only [hlam, hc124xy, hc467yz, htr012a, htr016a, htr145a, htr167a, htr345a, htr347a])
      obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd24b, hd78a, htr245a, htr345a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd24b, hd79a, htr245a, htr345a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc146zy, htr167a, htr467b, htr478a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr178a, htr178b, htr178c, _, _⟩
        linarith only [hlam, hc146zy, htr167c, htr178a, htr467a, htr678a])
      obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc124xy, hc478yz, htr012a, htr017a, htr145a, htr178a, htr345a, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hc146zy, htr167a, htr467b, htr479a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc146zy, htr167c, htr179a, htr467a, htr679a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hc124xy, hc789zy, htr012a, htr017a, htr145a, htr179a, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr489a, htr489b, htr489c, _, _⟩
        linarith only [hlam, hc124xy, hc578yz, htr012a, htr014c, htr017a, htr048a, htr178a, htr489a, htr589a])
      obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
      ·
        linarith only [hlam, hd46a, hd78b, htr346a, htr348a, htr489a, htr789a]

theorem shard_316 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr016b : m.d 0 1 < m.d 0 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr036a : m.d 3 6 + lam ≤ m.d 0 3)
    (htr037a : m.d 3 7 + lam ≤ m.d 0 3)
    (htr038a : m.d 3 8 + lam ≤ m.d 0 3)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr145a : m.d 4 5 + lam ≤ m.d 1 4)
    (htr245a : m.d 4 5 + lam ≤ m.d 2 4)
    (htr245c : m.d 2 5 < m.d 2 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    : False :=
  proof_shard_316 m htr012a htr013c htr014c htr015a htr016a htr016b htr017a htr017b htr018a htr018b htr025c htr036a htr037a htr038a htr045a htr045b htr124c htr125c htr126c htr127c htr145a htr245a htr245c htr345a htr345b htr345c htr456a htr456b htr456c

#print axioms shard_316
end Jsp404.NoSatElevenDBMTerminal
