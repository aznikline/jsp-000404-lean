import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_363 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr056a : m.d 5 6 + lam ≤ m.d 0 5)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd04a, hd04braw⟩ := m.hrange 0 4 (by decide)
  have hd04b : m.d 0 4 < 4*lam := by
    linarith only [hd04braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd18a, hd18braw⟩ := m.hrange 1 8 (by decide)
  have hd18b : m.d 1 8 < 4*lam := by
    linarith only [hd18braw, hp]
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
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
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc067xy, hc067yx, hc067yz, hc067zy⟩ := endpoint_caps m 0 6 7 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
  obtain ⟨hc129xy, hc129yx, hc129yz, hc129zy⟩ := endpoint_caps m 1 2 9 (by decide) (by decide)
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc158xy, hc158yx, hc158yz, hc158zy⟩ := endpoint_caps m 1 5 8 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7810xy, hc7810yx, hc7810yz, hc7810zy⟩ := endpoint_caps m 7 8 10 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  obtain ⟨hc8910xy, hc8910yx, hc8910yz, hc8910zy⟩ := endpoint_caps m 8 9 10 (by decide) (by decide)
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc457xy, htr045c, htr047a, htr056a, htr456a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, hc458xy, htr045c, htr048a, htr056a, htr456a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
    linarith only [hlam, hc459xy, htr045c, htr049a, htr056a, htr456a])
  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, hc345zy, htr036c, htr067a, htr356c, htr456a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc345zy, htr136c, htr167a, htr356c, htr456a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc345zy, htr356c, htr367a, htr456a, htr567a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr178a, htr678a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr078a, htr078b, htr078c, _, _⟩
      linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a])
    obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hd12a, hd79b, htr012a, htr016a, htr167a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hd12a, hd67b, htr012a, htr017a, htr179a, htr679a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    rcases m.htr 3 5 7 (by decide) (by decide) with
      ⟨htr357a, htr357b, htr357c, _, _⟩ | ⟨htr357a, htr357b, htr357c, _, _⟩
    ·
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc678yx, htr135c, htr156a, htr357a, htr567c, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr168a, htr168b, htr168c, _, _⟩
        linarith only [hlam, hc345zy, htr136c, htr168a, htr356c, htr456a, htr568a])
      obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc679yx, htr135c, htr156a, htr357a, htr567c, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr169a, htr169b, htr169c, _, _⟩
        linarith only [hlam, hc345zy, htr136c, htr169a, htr356c, htr456a, htr569a])
      obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
      have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
        linarith only [hlam, hc6710yx, htr135c, htr156a, htr357a, htr5610a, htr567c])
      obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
      have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
        linarith only [hlam, hc345zy, htr136c, htr1610a, htr356c, htr456a, htr5610a])
      obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
        linarith only [hlam, hd12a, hd89b, htr012a, htr016a, htr168a, htr689a])
      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
        linarith only [hlam, hd12a, hd68b, htr012a, htr018a, htr189a, htr689a])
      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
      have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
        linarith only [hlam, hd12a, hd910b, htr012a, htr016a, htr169a, htr6910a])
      obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
      rcases m.htr 7 8 9 (by decide) (by decide) with
        ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
      ·
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc467yz, htr478a, htr678c, htr689a, htr789a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc127xy, hc678zy, htr012a, htr016a, htr168a, htr179a, htr478a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc124xy, hc6910zy, htr012a, htr014c, htr016a, htr047a, htr1610a, htr479a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc128xy, hc679zy, htr012a, htr016a, htr169a, htr189a, htr7910a, htr8910a]
      ·
        have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr478a, htr478b, htr478c, _, _⟩
          linarith only [hlam, hc124xy, hc689zy, htr012a, htr014c, htr016a, htr047a, htr169a, htr478a, htr789a])
        obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc127xy, hc679zy, htr012a, htr016a, htr169a, htr178a, htr478a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc467yz, htr479a, htr679c, htr6910a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc127xy, hc689zy, htr012a, htr016a, htr169a, htr179a, htr7910a, htr8910a]
        ·
          linarith only [hlam, hc127xy, hc6910zy, htr012a, htr016a, htr1610a, htr178a, htr789a, htr8910a]
    ·
      have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr057a, htr057b, htr057c, _, _⟩
        linarith only [hlam, hc345zy, htr056a, htr057a, htr357a, htr456a])
      obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, htr057c, htr058b, htr078c])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hc345zy, htr137c, htr178a, htr357c, htr456a, htr567b, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hc345zy, htr137c, htr179a, htr357c, htr456a, htr567b, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      rcases m.htr 4 5 8 (by decide) (by decide) with
        ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
      ·
        rcases m.htr 4 5 9 (by decide) (by decide) with
          ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
        ·
          rcases m.htr 3 6 8 (by decide) (by decide) with
            ⟨htr368a, htr368b, htr368c, _, _⟩ | ⟨htr368a, htr368b, htr368c, _, _⟩
          ·
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hd12a, hd89b, htr012a, htr016a, htr136c, htr368a, htr689a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
              linarith only [hlam, hd12a, hd68b, htr012a, htr018a, htr189a, htr689a])
            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
            have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr589a, htr589b, htr589c, _, _⟩
              linarith only [hlam, hc345zy, htr137c, htr178c, htr189a, htr357c, htr458a, htr589a])
            obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
            have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
              linarith only [hlam, hd12a, hd810b, htr012a, htr016a, htr136c, htr368a, htr6810a])
            obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
              linarith only [hlam, hd12a, hd68b, htr012a, htr018a, htr1810a, htr6810a])
            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
            have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
              linarith only [hlam, hc345zy, htr137c, htr178c, htr1810a, htr357c, htr458a, htr5810a])
            obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc125xy, hc678zy, htr012a, htr015c, htr016a, htr058a, htr136c, htr368a, htr589a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr169a, htr169b, htr169c, _, _⟩
              linarith only [hlam, hc125xy, hc689zy, htr012a, htr015c, htr016a, htr057a, htr169a, htr578a, htr789a])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
              linarith only [hlam, hc125xy, hc678zy, htr012a, htr015c, htr016a, htr058a, htr136c, htr368a, htr5810a, htr7810a])
            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
              linarith only [hlam, hc125xy, hc8910yz, htr012a, htr015c, htr019a, htr057a, htr1910a, htr578a, htr7810a])
            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
              linarith only [hlam, hc679yx, htr167a, htr169c, htr1910a, htr6910a])
            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
            rcases m.htr 8 9 10 (by decide) (by decide) with
              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
            ·
              linarith only [hlam, hd67b, hd89a, htr167a, htr169a, htr6910a, htr8910a]
            ·
              linarith only [hlam, hd35b, hd910a, htr357a, htr578a, htr789a, htr8910a]
          ·
            have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr068a, htr068b, htr068c, _, _⟩
              linarith only [hlam, hc345zy, htr056b, htr068a, htr356c, htr368a, htr456a])
            obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
            have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr568a, htr568b, htr568c, _, _⟩
              linarith only [hlam, hc345zy, htr356c, htr368a, htr456a, htr568a])
            obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc345zy, htr356a, htr456b, htr468a, htr568a])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            rcases m.htr 5 6 9 (by decide) (by decide) with
              ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, hc678yx, htr067a, htr069a, htr568a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                linarith only [hlam, htr068c, htr069b, htr089c])
              obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc678yx, htr167a, htr169a, htr568a, htr569a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                linarith only [hlam, hc128xy, htr012a, htr018b, htr089a, htr189a])
              obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
              have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr469a, htr469b, htr469c, _, _⟩
                linarith only [hlam, htr456c, htr469a, htr569a])
              obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
              have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                linarith only [hlam, hc125xy, hc8910yx, htr012a, htr018a, htr156a, htr189a, htr568a, htr6810a])
              obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
              have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                linarith only [hlam, hc678yx, htr138c, htr1810a, htr367a, htr368c, htr6810a])
              obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
              have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                linarith only [hlam, hd12a, hd910b, htr012a, htr016a, htr169a, htr6910a])
              obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
              have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                linarith only [hlam, hc689xy, htr468a, htr469b, htr4910a, htr6910a])
              obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
              rcases m.htr 7 9 10 (by decide) (by decide) with
                ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
              ·
                linarith only [hlam, hc124xy, hc679zy, htr012a, htr014c, htr016a, htr049a, htr169a, htr4910a, htr7910a]
              ·
                linarith only [hlam, hc125xy, hc8910zy, htr012a, htr015c, htr018a, htr057a, htr1810a, htr579a, htr7910a]
            ·
              have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr069a, htr069b, htr069c, _, _⟩
                linarith only [hlam, htr056b, htr069a, htr569a])
              obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
              have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr169a, htr169b, htr169c, _, _⟩
                linarith only [hlam, hc125xy, htr012a, htr016a, htr156a, htr169a, htr569a])
              obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, hc678yx, htr0610a, htr067a, htr5610a, htr568a])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0610b, htr068c, htr0810c])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                  linarith only [hlam, htr0610b, htr069c, htr0910c])
                obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                  linarith only [hlam, hc128xy, htr012a, htr018b, htr0810a, htr1810a])
                obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                  linarith only [hlam, hc129xy, htr012a, htr019b, htr0910a, htr1910a])
                obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                  linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
                obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                  linarith only [hlam, hc678yx, htr138c, htr189a, htr367a, htr368c, htr689a])
                obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                rcases m.htr 8 9 10 (by decide) (by decide) with
                  ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                ·
                  linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
                ·
                  linarith only [hlam, hd12a, hd89b, htr012a, htr019a, htr1910a, htr8910a]
              ·
                rcases m.htr 3 8 9 (by decide) (by decide) with
                  ⟨htr389a, htr389b, htr389c, _, _⟩ | ⟨htr389a, htr389b, htr389c, _, _⟩
                ·
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc125xy, hc8910yx, htr012a, htr018a, htr138c, htr156a, htr389a, htr568a, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                    linarith only [hlam, hc678yx, htr138c, htr1810a, htr367a, htr368c, htr6810a])
                  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc125xy, hc8910zy, htr012a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                    linarith only [hlam, hc679yx, htr167a, htr169c, htr1910a, htr6910a])
                  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr138c, htr389a, htr8910a]
                  ·
                    linarith only [hlam, hd12a, hd89b, htr012a, htr019a, htr1910a, htr8910a]
                ·
                  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                    linarith only [hlam, hc678yx, htr367a, htr368c, htr389a, htr689a])
                  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                  have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                    linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
                  obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                  have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                    linarith only [hlam, hc678yx, htr138c, htr1810a, htr367a, htr368c, htr6810a])
                  obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                  have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                    linarith only [hlam, hc125xy, hc8910yz, htr012a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
                  obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                    linarith only [hlam, hc679yx, htr167a, htr169c, htr1910a, htr6910a])
                  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                  rcases m.htr 8 9 10 (by decide) (by decide) with
                    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                  ·
                    linarith only [hlam, hd35b, hd89a, htr356a, htr569a, htr6910a, htr8910a]
                  ·
                    linarith only [hlam, hd67b, hd910a, htr367a, htr368a, htr689a, htr8910a]
        ·
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            linarith only [hlam, hc569yz, htr456a, htr459a, htr569a]
          ·
            linarith only [hlam, hc679yx, htr456a, htr459a, htr567a, htr569b]
      ·
        rcases m.htr 5 6 8 (by decide) (by decide) with
          ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
        ·
          linarith only [hlam, hc568yz, htr456a, htr458a, htr568a]
        ·
          linarith only [hlam, hc678yx, htr456a, htr458a, htr567a, htr568b]
  ·
    have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr057a, htr057b, htr057c, _, _⟩
      linarith only [hlam, htr056a, htr057a, htr567c])
    obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
    have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr067a, htr067b, htr067c, _, _⟩
      linarith only [hlam, htr056b, htr067a, htr567a])
    obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
    have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr157a, htr157b, htr157c, _, _⟩
      linarith only [hlam, htr015c, htr056a, htr157a, htr567c])
    obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
    have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr167a, htr167b, htr167c, _, _⟩
      linarith only [hlam, hc125xy, htr012a, htr016a, htr156a, htr167a, htr567a])
    obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, htr135c, htr156a, htr357a, htr567c])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc345zy, htr356a, htr456b, htr467a, htr567a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 4 5 7 (by decide) (by decide) with
      ⟨htr457a, htr457b, htr457c, _, _⟩ | ⟨htr457a, htr457b, htr457c, _, _⟩
    ·
      rcases m.htr 5 6 8 (by decide) (by decide) with
        ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
      ·
        have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr058a, htr058b, htr058c, _, _⟩
          linarith only [hlam, hc678xy, htr056a, htr058a, htr567a, htr568c])
        obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, hc345zy, htr036c, htr068a, htr356c, htr456a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr078a, htr078b, htr078c, _, _⟩
          linarith only [hlam, htr067c, htr068b, htr078c])
        obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
        have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr168a, htr168b, htr168c, _, _⟩
          linarith only [hlam, hc345zy, htr136c, htr168a, htr356c, htr456a, htr568a])
        obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc127xy, htr012a, htr017b, htr078a, htr178a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr468a, htr468b, htr468c, _, _⟩
          linarith only [hlam, htr456c, htr468a, htr568a])
        obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc125xy, hc789yx, htr012a, htr017a, htr156a, htr178a, htr567a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
          linarith only [hlam, hc678xy, htr067c, htr068a, htr079a, htr679a])
        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc678xy, htr167c, htr168a, htr179a, htr679a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc579yz, htr057b, htr079a, htr457a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
          linarith only [hlam, hc125xy, hc7810yx, htr012a, htr017a, htr156a, htr178a, htr567a, htr6710a])
        obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
        have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
          linarith only [hlam, hc678xy, htr167c, htr168a, htr1710a, htr6710a])
        obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr012a, htr016a, htr168a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
          linarith only [hlam, hc678xy, htr058b, htr089a, htr567a, htr568b, htr689a])
        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
        have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr059a, htr059b, htr059c, _, _⟩
          linarith only [hlam, htr058c, htr059b, htr089c])
        obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
        have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr159a, htr159b, htr159c, _, _⟩
          linarith only [hlam, htr015c, htr059a, htr159a])
        obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hc678xy, htr467a, htr468b, htr489a, htr689a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd12a, hd910b, htr012a, htr017a, htr179a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hd12a, hd79b, htr012a, htr019a, htr1910a, htr7910a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc145zy, htr159c, htr1910a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc125xy, hc789zy, htr012a, htr015c, htr017a, htr059a, htr179a, htr5910a, htr8910a]
        ·
          linarith only [hlam, hc124xy, hc7910zy, htr012a, htr014c, htr017a, htr048a, htr1710a, htr489a, htr8910a]
      ·
        have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr068a, htr068b, htr068c, _, _⟩
          linarith only [hlam, htr056b, htr068a, htr568a])
        obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
        have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr158a, htr158b, htr158c, _, _⟩
          linarith only [hlam, htr015c, htr056a, htr158a, htr568c])
        obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
        rcases m.htr 4 5 8 (by decide) (by decide) with
          ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
        ·
          rcases m.htr 5 6 9 (by decide) (by decide) with
            ⟨htr569a, htr569b, htr569c, _, _⟩ | ⟨htr569a, htr569b, htr569c, _, _⟩
          ·
            have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr069a, htr069b, htr069c, _, _⟩
              linarith only [hlam, hc345zy, htr036c, htr069a, htr356c, htr456a, htr569a])
            obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
            have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr079a, htr079b, htr079c, _, _⟩
              linarith only [hlam, htr067c, htr069b, htr079c])
            obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
            have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr089a, htr089b, htr089c, _, _⟩
              linarith only [hlam, htr068c, htr069b, htr089c])
            obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
            have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr169a, htr169b, htr169c, _, _⟩
              linarith only [hlam, hc345zy, htr136c, htr169a, htr356c, htr456a, htr569a])
            obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
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
              linarith only [hlam, hc125xy, hc789xy, htr012a, htr017a, htr156a, htr179a, htr567a, htr678a])
            obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
            have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr178a, htr178b, htr178c, _, _⟩
              linarith only [hlam, hc679xy, htr167c, htr169a, htr178a, htr678a])
            obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a]
            ·
              linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a]
          ·
            rcases m.htr 4 5 9 (by decide) (by decide) with
              ⟨htr459a, htr459b, htr459c, _, _⟩ | ⟨htr459a, htr459b, htr459c, _, _⟩
            ·
              rcases m.htr 5 6 10 (by decide) (by decide) with
                ⟨htr5610a, htr5610b, htr5610c, _, _⟩ | ⟨htr5610a, htr5610b, htr5610c, _, _⟩
              ·
                have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
                  linarith only [hlam, hc345zy, htr036c, htr0610a, htr356c, htr456a, htr5610a])
                obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
                have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                  linarith only [hlam, htr0610b, htr067c, htr0710c])
                obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                  linarith only [hlam, htr0610b, htr068c, htr0810c])
                obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                have hforced1610 := (m.htr 1 6 10 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr1610a, htr1610b, htr1610c, _, _⟩
                  linarith only [hlam, hc345zy, htr136c, htr1610a, htr356c, htr456a, htr5610a])
                obtain ⟨htr1610a, htr1610b, htr1610c, _, _⟩ := hforced1610
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
                  linarith only [hlam, hc125xy, hc7810xy, htr012a, htr017a, htr156a, htr1710a, htr567a, htr678a])
                obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
                  rintro ⟨htr178a, htr178b, htr178c, _, _⟩
                  linarith only [hlam, hc6710xy, htr1610a, htr167c, htr178a, htr678a])
                obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
                rcases m.htr 7 8 10 (by decide) (by decide) with
                  ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                ·
                  linarith only [hlam, hd12a, hd810b, htr012a, htr017a, htr178a, htr7810a]
                ·
                  linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr1810a, htr7810a]
              ·
                rcases m.htr 4 5 10 (by decide) (by decide) with
                  ⟨htr4510a, htr4510b, htr4510c, _, _⟩ | ⟨htr4510a, htr4510b, htr4510c, _, _⟩
                ·
                  rcases m.htr 6 7 8 (by decide) (by decide) with
                    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
                  ·
                    rcases m.htr 3 7 8 (by decide) (by decide) with
                      ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
                    ·
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc124xy, htr012a, htr014c, htr017a, htr047a, htr137c, htr378a, htr478a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                        linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr137c, htr378a, htr789a])
                      obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                      have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                        linarith only [hlam, hd12a, hd78b, htr012a, htr018a, htr189a, htr789a])
                      obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                      have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                        linarith only [hlam, hc145zy, htr158c, htr189a, htr458a, htr589a])
                      obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                      have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                        linarith only [hlam, hc125xy, hc678yz, htr012a, htr017a, htr137c, htr156a, htr378a, htr568c, htr589a, htr689a])
                      obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                      have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                        linarith only [hlam, hc125xy, hc789zy, htr012a, htr017a, htr156a, htr179a, htr568a, htr689a])
                      obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                      have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                        linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
                      obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                        linarith only [hlam, hc145zy, htr157c, htr179a, htr457a, htr579a])
                      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                        linarith only [hlam, hc345zy, htr356a, htr457b, htr479a, htr567c, htr579a])
                      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                      have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                        linarith only [hlam, hc128xy, hc789yx, htr012a, htr017a, htr137c, htr1810a, htr378a, htr478b, htr479a, htr4810a])
                      obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                      have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                        linarith only [hlam, hc124xy, hc678yz, htr012a, htr014c, htr017a, htr048a, htr137c, htr378a, htr4810a, htr6810a])
                      obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                      have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                        linarith only [hlam, hc125xy, hc8910yz, htr012a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
                      obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                      have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                        linarith only [hlam, hc789yx, htr137c, htr179c, htr1910a, htr378a, htr7910a])
                      obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                      rcases m.htr 8 9 10 (by decide) (by decide) with
                        ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                      ·
                        linarith only [hlam, hd78b, hd89a, htr137c, htr179a, htr378a, htr7910a, htr8910a]
                      ·
                        linarith only [hlam, hd35b, hd910a, htr356a, htr568a, htr689a, htr8910a]
                    ·
                      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
                        linarith only [hlam, hc345zy, htr057b, htr078a, htr357c, htr378a, htr457a])
                      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
                      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                        linarith only [hlam, hc345zy, htr357c, htr378a, htr457a, htr578a])
                      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
                        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                        linarith only [hlam, hc345zy, htr356a, htr457b, htr478a, htr567c, htr578a])
                      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
                      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
                        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                        linarith only [hlam, hd35b, hd79a, htr356a, htr567c, htr578a, htr678a, htr679a])
                      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                      rcases m.htr 5 7 9 (by decide) (by decide) with
                        ⟨htr579a, htr579b, htr579c, _, _⟩ | ⟨htr579a, htr579b, htr579c, _, _⟩
                      ·
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, hc067zy, htr079a, htr578a, htr579a, htr678a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr089a, htr089b, htr089c, _, _⟩
                          linarith only [hlam, htr078c, htr079b, htr089c])
                        obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc167zy, htr179a, htr578a, htr579a, htr678a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                          linarith only [hlam, hc128xy, htr012a, htr018b, htr089a, htr189a])
                        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, htr457c, htr479a, htr579a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                          linarith only [hlam, hc125xy, hc8910yx, htr012a, htr018a, htr156a, htr189a, htr567c, htr578a, htr7810a])
                        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                          linarith only [hlam, hc367zy, htr138c, htr1810a, htr378c, htr678a, htr7810a])
                        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                          linarith only [hlam, hc125xy, hc8910zy, htr012a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
                        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                          linarith only [hlam, hc124xy, hc679yz, htr012a, htr014c, htr017a, htr049a, htr179a, htr4910a, htr6910a])
                        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                        rcases m.htr 8 9 10 (by decide) (by decide) with
                          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                        ·
                          linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
                        ·
                          linarith only [hlam, hd67a, hd89b, htr478a, htr479b, htr4910a, htr678a, htr8910a]
                      ·
                        have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr079a, htr079b, htr079c, _, _⟩
                          linarith only [hlam, htr057b, htr079a, htr579a])
                        obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
                        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                          linarith only [hlam, hc125xy, htr012a, htr017a, htr156a, htr179a, htr567c, htr579a])
                        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                          linarith only [hlam, hc567zy, htr478a, htr479a, htr579a, htr678a])
                        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
                        rcases m.htr 5 7 10 (by decide) (by decide) with
                          ⟨htr5710a, htr5710b, htr5710c, _, _⟩ | ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                        ·
                          have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
                            linarith only [hlam, hc067zy, htr0710a, htr5710a, htr578a, htr678a])
                          obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
                          have hforced0810 := (m.htr 0 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0810a, htr0810b, htr0810c, _, _⟩
                            linarith only [hlam, htr0710b, htr078c, htr0810c])
                          obtain ⟨htr0810a, htr0810b, htr0810c, _, _⟩ := hforced0810
                          have hforced0910 := (m.htr 0 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr0910a, htr0910b, htr0910c, _, _⟩
                            linarith only [hlam, htr0710b, htr079c, htr0910c])
                          obtain ⟨htr0910a, htr0910b, htr0910c, _, _⟩ := hforced0910
                          have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                            linarith only [hlam, hc128xy, htr012a, htr018b, htr0810a, htr1810a])
                          obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                            linarith only [hlam, hc129xy, htr012a, htr019b, htr0910a, htr1910a])
                          obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                          have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                            linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr567c, htr578a, htr789a])
                          obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                            linarith only [hlam, hc367zy, htr138c, htr189a, htr378c, htr678a, htr789a])
                          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                          rcases m.htr 8 9 10 (by decide) (by decide) with
                            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                          ·
                            linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
                          ·
                            linarith only [hlam, hd12a, hd89b, htr012a, htr019a, htr1910a, htr8910a]
                        ·
                          rcases m.htr 7 8 9 (by decide) (by decide) with
                            ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
                          ·
                            have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                              linarith only [hlam, hc367zy, htr138c, htr189a, htr378c, htr678a, htr789a])
                            obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                            have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                              linarith only [hlam, hc125xy, hc8910yx, htr012a, htr018a, htr156a, htr189a, htr567c, htr578a, htr7810a])
                            obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
                            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                              linarith only [hlam, hc367zy, htr138c, htr1810a, htr378c, htr678a, htr7810a])
                            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                            have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
                              linarith only [hlam, hc125xy, hc8910zy, htr012a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
                            obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
                            have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
                              linarith only [hlam, hc124xy, hc689yz, htr012a, htr014c, htr018a, htr049a, htr189a, htr4910a, htr6910a])
                            obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
                            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_right (by
                              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                              linarith only [hlam, hc167zy, htr179c, htr1910a, htr479b, htr4910a, htr679a])
                            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                            rcases m.htr 8 9 10 (by decide) (by decide) with
                              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                            ·
                              linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
                            ·
                              linarith only [hlam, hd12a, hd89b, htr012a, htr019a, htr1910a, htr8910a]
                          ·
                            have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
                              linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr567c, htr578a, htr789a])
                            obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
                            have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                              linarith only [hlam, hc367zy, htr138c, htr1810a, htr378c, htr478b, htr4810a, htr678a])
                            obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
                              linarith only [hlam, hc367zy, htr378a, htr678b, htr689a, htr789a])
                            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
                            have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
                              linarith only [hlam, hd04b, hd89a, htr048a, htr4810a, htr6810a, htr689a])
                            obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
                            have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                              linarith only [hlam, hc125xy, hc8910yz, htr012a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
                            obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                            have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
                              rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                              linarith only [hlam, hc167zy, htr179c, htr1910a, htr679a, htr7910a])
                            obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                            rcases m.htr 8 9 10 (by decide) (by decide) with
                              ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                            ·
                              linarith only [hlam, hd35b, hd89a, htr356a, htr567c, htr579a, htr7910a, htr8910a]
                            ·
                              linarith only [hlam, hd35b, hd910a, htr356a, htr567c, htr578a, htr789a, htr8910a]
                  ·
                    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
                      linarith only [hlam, hc125xy, hc789xy, htr012a, htr017a, htr156a, htr179a, htr567a, htr678a])
                    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
                    have hforced1710 := (m.htr 1 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1710a, htr1710b, htr1710c, _, _⟩
                      linarith only [hlam, hc125xy, hc7810xy, htr012a, htr017a, htr156a, htr1710a, htr567a, htr678a])
                    obtain ⟨htr1710a, htr1710b, htr1710c, _, _⟩ := hforced1710
                    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                      linarith only [hlam, hc145zy, htr157c, htr179a, htr457a, htr579a])
                    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
                    have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                      linarith only [hlam, hc145zy, htr157c, htr1710a, htr457a, htr5710a])
                    obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                      linarith only [hlam, hd35b, hd78a, htr356a, htr567c, htr579a, htr678a, htr679a])
                    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
                    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
                      linarith only [hlam, hc125xy, hc789yz, htr012a, htr018a, htr156a, htr189a, htr567a, htr679a])
                    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
                    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                      linarith only [hlam, hc145zy, htr158c, htr189a, htr458a, htr589a])
                    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
                    have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                      linarith only [hlam, hd35b, hd78a, htr356a, htr567c, htr5710a, htr6710a, htr678a])
                    obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                    have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
                      rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
                      linarith only [hlam, hc125xy, hc7910yz, htr012a, htr019a, htr156a, htr1910a, htr567a, htr6710a])
                    obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
                    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
                      linarith only [hlam, hd35b, hd89a, htr356a, htr567a, htr678a, htr789a])
                    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
                    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                      linarith only [hlam, hd35b, hd910a, htr356a, htr567a, htr679a, htr7910a])
                    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
                    rcases m.htr 8 9 10 (by decide) (by decide) with
                      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                    ·
                      linarith only [hlam, hc178zy, htr189c, htr1910a, htr789a, htr8910a]
                    ·
                      linarith only [hlam, hd35b, hd79a, htr356a, htr568c, htr589a, htr7910a, htr8910a]
                ·
                  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
                    linarith only [hlam, htr4510c, htr457b, htr4710b])
                  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
                  have hforced4810 := (m.htr 4 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr4810a, htr4810b, htr4810c, _, _⟩
                    linarith only [hlam, htr4510c, htr458b, htr4810b])
                  obtain ⟨htr4810a, htr4810b, htr4810c, _, _⟩ := hforced4810
                  have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
                    linarith only [hlam, htr457c, htr4710a, htr5710a])
                  obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
                  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                    linarith only [hlam, hc7810yx, htr4510a, htr457a, htr5710b, htr578a])
                  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
                  have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
                    linarith only [hlam, htr458c, htr4810a, htr5810a])
                  obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
                  have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
                    linarith only [hlam, hd35b, hd67a, htr356a, htr4510a, htr456a, htr5710b, htr6710a])
                  obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
                  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                    linarith only [hlam, hd35b, hd710a, htr356a, htr567c, htr578a, htr6710a, htr678a])
                  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
                  rcases m.htr 7 8 10 (by decide) (by decide) with
                    ⟨htr7810a, htr7810b, htr7810c, _, _⟩ | ⟨htr7810a, htr7810b, htr7810c, _, _⟩
                  ·
                    linarith only [hlam, hd35b, hd78a, htr356a, htr4510a, htr456a, htr5810b, htr7810a]
                  ·
                    linarith only [hlam, hd35b, hd810a, htr356a, htr567a, htr678a, htr7810a]
            ·
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, htr457b, htr459c, htr479b])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr489a, htr489b, htr489c, _, _⟩
                linarith only [hlam, htr458b, htr459c, htr489b])
              obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
              have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr579a, htr579b, htr579c, _, _⟩
                linarith only [hlam, htr457c, htr479a, htr579a])
              obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
              have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr578a, htr578b, htr578c, _, _⟩
                linarith only [hlam, hc789yx, htr457a, htr459a, htr578a, htr579b])
              obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
              have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr589a, htr589b, htr589c, _, _⟩
                linarith only [hlam, htr458c, htr489a, htr589a])
              obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
              have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr679a, htr679b, htr679c, _, _⟩
                linarith only [hlam, hd35b, hd67a, htr356a, htr456a, htr459a, htr579b, htr679a])
              obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
              have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr678a, htr678b, htr678c, _, _⟩
                linarith only [hlam, hd35b, hd79a, htr356a, htr567c, htr578a, htr678a, htr679a])
              obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
              rcases m.htr 7 8 9 (by decide) (by decide) with
                ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
              ·
                linarith only [hlam, hd35b, hd78a, htr356a, htr456a, htr459a, htr589b, htr789a]
              ·
                linarith only [hlam, hd35b, hd89a, htr356a, htr567a, htr678a, htr789a]
        ·
          have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr478a, htr478b, htr478c, _, _⟩
            linarith only [hlam, htr457b, htr458c, htr478b])
          obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
          have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr578a, htr578b, htr578c, _, _⟩
            linarith only [hlam, htr457c, htr478a, htr578a])
          obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
          have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr579a, htr579b, htr579c, _, _⟩
            linarith only [hlam, hc789xy, htr457a, htr458a, htr578b, htr579a])
          obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
          have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
            linarith only [hlam, hc7810xy, htr457a, htr458a, htr5710a, htr578b])
          obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
          have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr589a, htr589b, htr589c, _, _⟩
            linarith only [hlam, hd35b, hd89a, htr356a, htr456a, htr458a, htr589a])
          obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
          have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr678a, htr678b, htr678c, _, _⟩
            linarith only [hlam, hd35b, hd67a, htr356a, htr456a, htr458a, htr578b, htr678a])
          obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
          have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr679a, htr679b, htr679c, _, _⟩
            linarith only [hlam, hd35b, hd78a, htr356a, htr567c, htr579a, htr678a, htr679a])
          obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
          have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr189a, htr189b, htr189c, _, _⟩
            linarith only [hlam, hc125xy, hc789yz, htr012a, htr018a, htr156a, htr189a, htr567a, htr679a])
          obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
          have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr459a, htr459b, htr459c, _, _⟩
            linarith only [hlam, hc158zy, htr189a, htr458a, htr459a, htr589c])
          obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
          have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
            linarith only [hlam, hd35b, hd910a, htr356a, htr456a, htr459a, htr5910a])
          obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hd35b, hd78a, htr356a, htr567c, htr5710a, htr6710a, htr678a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
            linarith only [hlam, hc125xy, hc7910yz, htr012a, htr019a, htr156a, htr1910a, htr567a, htr6710a])
          obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc158zy, htr189c, htr1910a, htr589a, htr8910a]
          ·
            linarith only [hlam, hc158zy, htr189a, htr589b, htr5910a, htr8910a]
    ·
      have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr058a, htr058b, htr058c, _, _⟩
        linarith only [hlam, hc578xy, htr056a, htr058a, htr456a, htr457a])
      obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
      have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr059a, htr059b, htr059c, _, _⟩
        linarith only [hlam, hc579xy, htr056a, htr059a, htr456a, htr457a])
      obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
      have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr568a, htr568b, htr568c, _, _⟩
        linarith only [hlam, hc678xy, htr456a, htr457a, htr567b, htr568a])
      obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
      have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr569a, htr569b, htr569c, _, _⟩
        linarith only [hlam, hc679xy, htr456a, htr457a, htr567b, htr569a])
      obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
      have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr578a, htr578b, htr578c, _, _⟩
        linarith only [hlam, hd35b, hd78a, htr356a, htr456a, htr457a, htr578a])
      obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
      have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr579a, htr579b, htr579c, _, _⟩
        linarith only [hlam, hd35b, hd79a, htr356a, htr456a, htr457a, htr579a])
      obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
      rcases m.htr 4 5 8 (by decide) (by decide) with
        ⟨htr458a, htr458b, htr458c, _, _⟩ | ⟨htr458a, htr458b, htr458c, _, _⟩
      ·
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc157zy, htr178a, htr457a, htr458a, htr578c])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd12a, hd89b, htr012a, htr017a, htr178a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd57a, hd78b, htr457a, htr458a, htr589a, htr789a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc125xy, hc678yz, htr012a, htr015c, htr017a, htr058a, htr178a, htr589a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr179a, htr179b, htr179c, _, _⟩
          linarith only [hlam, hc125xy, hc789zy, htr012a, htr017a, htr156a, htr179a, htr568a, htr689a])
        obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc125xy, hc8910xy, htr012a, htr018a, htr156a, htr1810a, htr568a, htr689a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc157zy, htr179a, htr457a, htr459a, htr579c])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd18b, hd57a, htr1810a, htr457a, htr458a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hd35b, hd910a, htr356a, htr456a, htr459a, htr5910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        have hforced6810 := (m.htr 6 8 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6810a, htr6810b, htr6810c, _, _⟩
          linarith only [hlam, hc125xy, hc678yz, htr012a, htr015c, htr017a, htr058a, htr178a, htr5810a, htr6810a])
        obtain ⟨htr6810a, htr6810b, htr6810c, _, _⟩ := hforced6810
        have hforced1910 := (m.htr 1 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr1910a, htr1910b, htr1910c, _, _⟩
          linarith only [hlam, hc125xy, hc8910yz, htr012a, htr019a, htr156a, htr1910a, htr568a, htr6810a])
        obtain ⟨htr1910a, htr1910b, htr1910c, _, _⟩ := hforced1910
        rcases m.htr 7 9 10 (by decide) (by decide) with
          ⟨htr7910a, htr7910b, htr7910c, _, _⟩ | ⟨htr7910a, htr7910b, htr7910c, _, _⟩
        ·
          linarith only [hlam, hc157zy, htr179c, htr1910a, htr579a, htr7910a]
        ·
          linarith only [hlam, hc157zy, htr179a, htr579b, htr5910a, htr7910a]
      ·
        have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr178a, htr178b, htr178c, _, _⟩
          linarith only [hlam, hc125xy, hc578yz, htr012a, htr017a, htr156a, htr178a, htr456a, htr458a])
        obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hd35b, hd89a, htr356a, htr456a, htr458a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced5810 := (m.htr 5 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5810a, htr5810b, htr5810c, _, _⟩
          linarith only [hlam, hd35b, hd810a, htr356a, htr456a, htr458a, htr5810a])
        obtain ⟨htr5810a, htr5810b, htr5810c, _, _⟩ := hforced5810
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc157zy, htr178a, htr578b, htr589a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr189a, htr189b, htr189c, _, _⟩
          linarith only [hlam, hc157zy, htr178c, htr189a, htr578a, htr789a])
        obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
        have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr459a, htr459b, htr459c, _, _⟩
          linarith only [hlam, hc125xy, hc589yz, htr012a, htr018a, htr156a, htr189a, htr456a, htr459a])
        obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
        have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
          linarith only [hlam, hc157zy, htr178a, htr578b, htr5810a, htr7810a])
        obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
        have hforced1810 := (m.htr 1 8 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr1810a, htr1810b, htr1810c, _, _⟩
          linarith only [hlam, hc157zy, htr178c, htr1810a, htr578a, htr7810a])
        obtain ⟨htr1810a, htr1810b, htr1810c, _, _⟩ := hforced1810
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc125xy, hc8910zy, htr012a, htr018a, htr156a, htr1810a, htr569a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
          linarith only [hlam, hc125xy, hc689yz, htr012a, htr015c, htr018a, htr059a, htr189a, htr5910a, htr6910a])
        obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd12a, hd910b, htr012a, htr018a, htr189a, htr8910a]
        ·
          linarith only [hlam, hd57a, hd89b, htr457a, htr459a, htr5910a, htr8910a]

theorem shard_363 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr017b : m.d 0 1 < m.d 0 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr018b : m.d 0 1 < m.d 0 8)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr056a : m.d 5 6 + lam ≤ m.d 0 5)
    (htr056b : m.d 5 6 < m.d 0 6)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138c : m.d 1 8 < m.d 3 8)
    (htr156a : m.d 5 6 + lam ≤ m.d 1 5)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr456a : m.d 4 5 + lam ≤ m.d 5 6)
    (htr456b : m.d 4 5 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 5 6)
    : False :=
  proof_shard_363 m htr012a htr014c htr015c htr016a htr017a htr017b htr018a htr018b htr019a htr019b htr036c htr045c htr056a htr056b htr135c htr136c htr137c htr138c htr156a htr356a htr356c htr456a htr456b htr456c

#print axioms shard_363
end Jsp404.NoSatElevenDBMTerminal
