import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_337 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr038c : m.d 0 8 < m.d 0 3)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd37a := (m.hrange 3 7 (by decide)).1
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
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
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
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr035b, htr045c, htr356a, htr456a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd12a, hd67b, htr012a, htr015a, htr145c, htr456a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr167a, htr567a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd12a, hd68b, htr012a, htr015a, htr145c, htr456a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr168a, htr568a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hd12a, hd69b, htr012a, htr015a, htr145c, htr456a, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, hd12a, hd56b, htr012a, htr016a, htr169a, htr569a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  rcases m.htr 4 5 7 (by decide) (by decide) with
    ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
  ·
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd12a, hd78b, htr012a, htr015a, htr145c, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd12a, hd57b, htr012a, htr017a, htr178a, htr578a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd12a, hd79b, htr012a, htr015a, htr145c, htr457a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd12a, hd57b, htr012a, htr017a, htr179a, htr579a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd12a, hd89b, htr012a, htr015a, htr145c, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
        linarith only [hlam, hd12a, hd810b, htr012a, htr015a, htr145c, htr458a, htr5810a])
      obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
      rcases m.htr 6 7 8 (by decide) (by decide) with
        ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
      ·
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc356yz, htr367a, htr567c, htr578a, htr678a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc126xy, hc567zy, htr012a, htr015a, htr145c, htr168a, htr367a, htr368a, htr457a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc127xy, hc568zy, htr012a, htr015a, htr145c, htr178a, htr458a, htr689a, htr789a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, hc123xy, hc589zy, htr012a, htr015a, htr136a, htr159a, htr368a, htr689a])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc567zy, htr578c, htr5810a, htr678a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc127xy, hc568zy, htr012a, htr015a, htr145c, htr178a, htr458a, htr6810a, htr7810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hc123xy, hc8910yz, htr012a, htr019a, htr136a, htr1910a, htr368a, htr6810a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc569yx, htr145c, htr159c, htr1910a, htr456a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd56b, hd89a, htr145c, htr159a, htr456a, htr5910a, htr8910a]
        ·
          linarith only [hlam, hd13b, hd910a, htr136a, htr368a, htr689a, htr8910a]
      ·
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hc123xy, hc578zy, htr012a, htr015a, htr136a, htr145c, htr367a, htr458a, htr678a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc126xy, hc568zy, htr012a, htr015a, htr145c, htr167a, htr367a, htr368a, htr458a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc356yz, htr368a, htr568c, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc356yz, htr368a, htr568c, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc126xy, hc578zy, htr012a, htr015a, htr145c, htr168a, htr458a, htr689a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, hc126xy, hc589zy, htr012a, htr015a, htr159a, htr167a, htr678a, htr789a])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc356yz, htr145c, htr159a, htr369a, htr456a, htr569b])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hd56b, hd910a, htr367a, htr369a, htr567a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd56b, hd69a, htr145c, htr159a, htr456a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hc569yx, htr145c, htr159c, htr1910a, htr456a, htr5910a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        rcases m.htr 7 8 10 (by decide) (by decide) with
          ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
        ·
          linarith only [hlam, hc126xy, hc578zy, htr012a, htr015a, htr145c, htr168a, htr458a, htr6810a, htr7810a]
        ·
          linarith only [hlam, hc126xy, hc8910yz, htr012a, htr019a, htr167a, htr1910a, htr678a, htr7810a]
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hd12a, hd56b, htr012a, htr015b, htr058a, htr456a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc356yz, htr368a, htr456a, htr458a, htr568b])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc567zy, htr457a, htr458a, htr578b, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 3 6 7 (by decide) (by decide) with
        ⟨htr367a, htr367b, htr367c, _, _⟩ | ⟨htr367a, htr367b, htr367c, _, _⟩
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc568yx, htr356b, htr358a, htr367a, htr567a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc356yz, htr367a, htr567c, htr579a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd56b, hd89a, htr367a, htr368a, htr567a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd56b, hd68a, htr456a, htr458a, htr589a, htr689a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc568yx, htr148c, htr189a, htr456a, htr458c, htr589a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc126xy, hc689yz, htr012a, htr018a, htr167a, htr189a, htr367a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc356yz, htr045c, htr059a, htr369a, htr456a, htr569b])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc8910yx, htr058a, htr059a, htr5810a, htr589c])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc568yx, htr148c, htr1810a, htr456a, htr458c, htr5810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd35a, hd910b, htr058a, htr059a, htr358a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc356yz, htr369a, htr569c, htr5910a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc126xy, hc789yz, htr012a, htr018a, htr169a, htr189a, htr6910a, htr7910a]
        ·
          linarith only [hlam, hc126xy, hc8910zy, htr012a, htr018a, htr167a, htr1810a, htr679a, htr7910a]
      ·
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc126xy, hc567zy, htr012a, htr015a, htr145c, htr169a, htr367a, htr369a, htr457a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd13b, hd89a, htr136a, htr367a, htr678a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc568yx, htr148c, htr189a, htr456a, htr458c, htr589a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc123xy, hc789yz, htr012a, htr018a, htr136a, htr189a, htr367a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, hc567zy, htr045c, htr059a, htr457a, htr579b, htr679a])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, hc568yx, htr058a, htr059a, htr145c, htr159a, htr456a])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hc8910yx, htr058a, htr059a, htr5810a, htr589c])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc568yx, htr148c, htr1810a, htr456a, htr458c, htr5810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd12a, hd910b, htr012a, htr015a, htr159a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc123xy, hc8910zy, htr012a, htr018a, htr136a, htr1810a, htr369a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc567zy, htr579c, htr5910a, htr679a, htr7910a]
        ·
          linarith only [hlam, hc127xy, hc689yz, htr012a, htr018a, htr179a, htr189a, htr6910a, htr7910a]
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, hd12a, hd56b, htr012a, htr015b, htr057a, htr456a, htr457a])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc356yz, htr367a, htr456a, htr457a, htr567b])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    rcases m.htr 4 5 8 (by decide) (by decide) with
      ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr045c, htr058a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, htr057c, htr058b, htr078c])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, htr057b, htr078a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc789yx, htr045c, htr057a, htr458a, htr578c, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
        linarith only [hlam, hc567yx, htr147c, htr179a, htr456a, htr457c, htr579a])
      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
      have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
        linarith only [hlam, hc7810yx, htr045c, htr057a, htr458a, htr5710a, htr578c])
      obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
      have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
        linarith only [hlam, hc567yx, htr147c, htr1710a, htr456a, htr457c, htr5710a])
      obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
        linarith only [hlam, hd12a, hd89b, htr012a, htr015a, htr145c, htr458a, htr589a])
      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
      have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr089a, htr089b, htr089c, _, _⟩
        linarith only [hlam, hc578xy, htr057a, htr058b, htr089a, htr589a])
      obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
        linarith only [hlam, htr578c, htr589a, htr789a])
      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        linarith only [hlam, hd12a, hd910b, htr012a, htr017a, htr179a, htr7910a])
      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
      rcases m.htr 8 9 10 (by decide) (by decide) with
        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
      ·
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc123xy, hc789zy, htr012a, htr017a, htr136a, htr179a, htr368a, htr689a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc126xy, hc679yz, htr012a, htr017a, htr168a, htr179a, htr368a, htr369a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        rcases m.htr 6 9 10 (by decide) (by decide) with
          ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        ·
          linarith only [hlam, hd67a, hd79b, htr367a, htr369a, htr6910a, htr7910a]
        ·
          linarith only [hlam, hc126xy, hc789zy, htr012a, htr017a, htr169a, htr179a, htr6910a, htr8910a]
      ·
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc126xy, hc7910zy, htr012a, htr017a, htr168a, htr1710a, htr689a, htr8910a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr368a, htr368b, htr368c, _, _⟩
          linarith only [hlam, hc356yz, htr368a, htr568c, htr589a, htr689a])
        obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
        have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr369a, htr369b, htr369c, _, _⟩
          linarith only [hlam, hc126xy, hc568zy, htr012a, htr015a, htr145c, htr169a, htr368a, htr369a, htr458a])
        obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
        rcases m.htr 6 9 10 (by decide) (by decide) with
          ⟨htr6910a, htr6910b, htr6910c, _, _⟩ | ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        ·
          linarith only [hlam, hc123xy, hc679yz, htr012a, htr013c, htr017a, htr038c, htr089a, htr179a, htr6910a, htr8910a]
        ·
          linarith only [hlam, hc123xy, hc7910zy, htr012a, htr017a, htr136a, htr1710a, htr369a, htr6910a]
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc567yx, htr057a, htr058a, htr456a, htr458a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc356yz, htr368a, htr456a, htr458a, htr568b])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      rcases m.htr 3 5 7 (by decide) (by decide) with
        ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
      ·
        rcases m.htr 4 5 9 (by decide) (by decide) with
          ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
        ·
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr045c, htr059a, htr459a])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr057c, htr059b, htr079c])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
            linarith only [hlam, htr058c, htr059b, htr089c])
          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc128xy, htr012a, htr018b, htr089a, htr189a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, htr057b, htr079a, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc789xy, htr045c, htr057a, htr459a, htr578a, htr579c])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc567yx, htr147c, htr178a, htr456a, htr457c, htr578a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
          ·
            linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
        ·
          rcases m.htr 4 5 10 (by decide) (by decide) with
            ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
          ·
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, htr045c, htr0510a, htr4510a])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0510b, htr057c, htr0710c])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
              linarith only [hlam, htr0510b, htr058c, htr0810c])
            obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
              linarith only [hlam, hc128xy, htr012a, htr018b, htr0810a, htr1810a])
            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
            have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
              linarith only [hlam, htr057b, htr0710a, htr5710a])
            obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc7810xy, htr045c, htr057a, htr4510a, htr5710c, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc567yx, htr147c, htr178a, htr456a, htr457c, htr578a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            rcases m.htr 7 8 10 (by decide) (by decide) with
              ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd810b, htr012a, htr017a, htr178a, htr7810a]
            ·
              linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr1810a, htr7810a]
          ·
            rcases m.htr 5 7 8 (by decide) (by decide) with
              ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
            ·
              have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                linarith only [hlam, hc567yx, htr147c, htr178a, htr456a, htr457c, htr578a])
              obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hc123xy, hc789yx, htr012a, htr017a, htr136a, htr178a, htr367a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr579a, htr679a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc567yx, htr147c, htr179a, htr456a, htr457c, htr579a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                linarith only [hlam, hc123xy, hc789zy, htr012a, htr017a, htr136a, htr179a, htr368a, htr689a])
              obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hd56b, hd68a, htr456a, htr458a, htr589a, htr689a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc568yx, htr148c, htr189a, htr456a, htr458c, htr589a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
              ·
                linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
            ·
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hd37a, hd56b, htr378a, htr456a, htr457a, htr578a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd56b, hd67a, htr456a, htr457a, htr578a, htr678a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc123xy, hc789xy, htr012a, htr017a, htr136a, htr179a, htr367a, htr678a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hd56b, hd78a, htr147c, htr179a, htr378a, htr379a, htr456a, htr457c])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd56b, hd78a, htr357c, htr379a, htr456a, htr457a, htr678a, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc123xy, hc789yz, htr012a, htr018a, htr136a, htr189a, htr367a, htr679a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568yx, htr148c, htr189a, htr456a, htr458c, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a]
              ·
                linarith only [hlam, hd56b, hd89a, htr456a, htr457a, htr578a, htr789a]
      ·
        have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr358a, htr358b, htr358c, _, _⟩
          linarith only [hlam, hc567yx, htr357a, htr358a, htr456a, htr458a])
        obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
        rcases m.htr 4 5 9 (by decide) (by decide) with
          ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
        ·
          have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr059a, htr059b, htr059c, _, _⟩
            linarith only [hlam, htr045c, htr059a, htr459a])
          obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
          have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr079a, htr079b, htr079c, _, _⟩
            linarith only [hlam, htr057c, htr059b, htr079c])
          obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
          have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr089a, htr089b, htr089c, _, _⟩
            linarith only [hlam, htr058c, htr059b, htr089c])
          obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
          have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr179a, htr179b, htr179c, _, _⟩
            linarith only [hlam, hc127xy, htr012a, htr017b, htr079a, htr179a])
          obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc128xy, htr012a, htr018b, htr089a, htr189a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, hc123xy, hc789xy, htr012a, htr017a, htr135a, htr179a, htr357a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr178a, htr178b, htr178c, _, _⟩
            linarith only [hlam, hc567yx, htr147c, htr178a, htr456a, htr457c, htr578a])
          obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
          rcases m.htr 7 8 9 (by decide) (by decide) with
            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
          ·
            linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
          ·
            linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
        ·
          rcases m.htr 4 5 10 (by decide) (by decide) with
            ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
          ·
            have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
              linarith only [hlam, htr045c, htr0510a, htr4510a])
            obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
            have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
              linarith only [hlam, htr0510b, htr057c, htr0710c])
            obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
            have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
              linarith only [hlam, htr0510b, htr058c, htr0810c])
            obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
            have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
              linarith only [hlam, hc127xy, htr012a, htr017b, htr0710a, htr1710a])
            obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
              linarith only [hlam, hc128xy, htr012a, htr018b, htr0810a, htr1810a])
            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
            have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr578a, htr578b, htr578c, _, _⟩
              linarith only [hlam, hc123xy, hc7810xy, htr012a, htr017a, htr135a, htr1710a, htr357a, htr578a])
            obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc567yx, htr147c, htr178a, htr456a, htr457c, htr578a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            rcases m.htr 7 8 10 (by decide) (by decide) with
              ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd810b, htr012a, htr017a, htr178a, htr7810a]
            ·
              linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr1810a, htr7810a]
          ·
            rcases m.htr 4 7 8 (by decide) (by decide) with
              ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
            ·
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc123xy, hc789yx, htr012a, htr017a, htr135a, htr147c, htr357a, htr478a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc567yx, htr147c, htr179a, htr456a, htr457c, htr579a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc123xy, hc789zy, htr012a, htr017a, htr135a, htr179a, htr358a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc568yx, htr148c, htr189a, htr456a, htr458c, htr589a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr147c, htr478a, htr789a]
              ·
                linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
            ·
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc567yx, htr456a, htr457c, htr478a, htr578a])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                linarith only [hlam, hc123xy, hc789xy, htr012a, htr017a, htr135a, htr179a, htr357a, htr578a])
              obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, hc567yx, htr147c, htr179a, htr456a, htr457c, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc123xy, hc789yz, htr012a, htr018a, htr135a, htr189a, htr357a, htr579a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, hc568yx, htr148c, htr189a, htr456a, htr458c, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd56b, hd78a, htr456a, htr458a, htr589a, htr789a]
              ·
                linarith only [hlam, hd56b, hd89a, htr456a, htr457a, htr578a, htr789a]

theorem shard_337 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr015b : m.d 0 1 < m.d 0 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr035b : m.d 3 5 < m.d 0 5)
    (htr038c : m.d 0 8 < m.d 0 3)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr145c : m.d 1 5 < m.d 4 5)
    (htr147c : m.d 1 7 < m.d 4 7)
    (htr148c : m.d 1 8 < m.d 4 8)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    : False :=
  proof_shard_337 m htr012a htr013c htr015a htr015b htr016a htr017a htr017b htr018a htr018b htr019a htr035b htr038c htr045c htr135a htr136a htr145c htr147c htr148c htr456a

#print axioms shard_337
end Jsp404.NoSatElevenDBMTerminal
