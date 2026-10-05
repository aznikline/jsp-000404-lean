import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_155 {lam p : ℝ} (m : ElevenModel lam p)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd23a := (m.hrange 2 3 (by decide)).1
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd56a, hd56braw⟩ := m.hrange 5 6 (by decide)
  have hd56b : m.d 5 6 < 4*lam := by
    linarith only [hd56braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr135c, htr136b, htr156c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr135b, htr156a, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc567yx, htr135a, htr136a, htr356c, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc568yx, htr135a, htr136a, htr356c, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hc569yx, htr135a, htr136a, htr356c, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced3510 := (m.htr 3 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr3510a, htr3510b, htr3510c, _, _⟩
    linarith only [hlam, hc5610yx, htr135a, htr136a, htr3510a, htr356c])
  obtain ⟨htr3510a, htr3510b, htr3510c, _, _⟩ := hforced3510
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd23a, hd67b, htr134a, htr136a, htr234a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd23a, hd45b, htr134a, htr136a, htr234a, htr356c, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr234a, htr345b, htr357a, htr456a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr234a, htr345b, htr358a, htr456a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr234a, htr345b, htr359a, htr456a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hd23a, hd56b, htr234a, htr345b, htr3510a, htr4510a, htr456a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, htr356c, htr367a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd23a, hd78b, htr234a, htr345a, htr457a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hd23a, hd79b, htr234a, htr345a, htr457a, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
    linarith only [hlam, hd23a, hd89b, htr234a, htr345a, htr458a, htr589a])
  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
    linarith only [hlam, hd23a, hd910b, htr234a, htr345a, htr459a, htr5910a])
  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
  rcases m.htr 2 6 7 (by decide) (by decide) with
    ⟨htr267a, htr267b, htr267c, _, _⟩ | ⟨htr267a, htr267b, htr267c, _, _⟩
  ·
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hc256yz, htr267a, htr567c, htr578a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hc236yz, htr267b, htr278a, htr367a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc256yz, htr267a, htr567c, htr579a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hc236yz, htr267b, htr279a, htr367a, htr679a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, hc023yx, hc589zy, htr027a, htr034a, htr278a, htr345a, htr459a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hc023yx, hc5910zy, htr027a, htr034a, htr279a, htr345a, htr4510a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      linarith only [hlam, hc578zy, htr589c, htr5910a, htr789a, htr8910a]
    ·
      linarith only [hlam, hc578zy, htr589a, htr789b, htr7910a, htr8910a]
  ·
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hc023yx, hc578zy, htr026a, htr034a, htr267a, htr345a, htr458a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hc567zy, htr267a, htr268a, htr578a, htr678c])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hc023yx, hc589zy, htr026a, htr034a, htr268a, htr345a, htr459a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hc567zy, htr578c, htr589a, htr678a, htr789a]
    ·
      linarith only [hlam, hc567zy, htr578a, htr678b, htr689a, htr789a]

theorem shard_155 {lam p : ℝ} (m : ElevenModel lam p)
    (htr026a : m.d 2 6 + lam ≤ m.d 0 2)
    (htr027a : m.d 2 7 + lam ≤ m.d 0 2)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    : False :=
  proof_shard_155 m htr026a htr027a htr034a htr134a htr135a htr135b htr135c htr136a htr136b htr234a htr345a htr345b

#print axioms shard_155
end Jsp404.NoSatElevenDBMTerminal
