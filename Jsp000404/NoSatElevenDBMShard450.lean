import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_450 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046a : m.d 0 4 + lam ≤ m.d 4 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr047b : m.d 0 4 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr349a : m.d 4 9 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc469xy, hc469yx, hc469yz, hc469zy⟩ := endpoint_caps m 4 6 9 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
    linarith only [hlam, htr034b, htr049a, htr349a])
  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr045b, htr049c, htr059b])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr046b, htr049c, htr069b])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
    linarith only [hlam, htr047b, htr049c, htr079b])
  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
  have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr149a, htr149b, htr149c, _, _⟩
    linarith only [hlam, hc123yz, htr134b, htr149a, htr234a, htr349a])
  obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, htr045c, htr059a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc569yx, htr034b, htr045a, htr349a, htr456a, htr459b])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc459yx, htr145b, htr149a, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, htr046c, htr069a, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hc679yx, htr034b, htr046a, htr349a, htr467a, htr469b])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc469yx, htr146b, htr149a, htr167a, htr467a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
    linarith only [hlam, htr047c, htr079a, htr479a])
  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hc456zy, htr346a, htr349a, htr469b, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd01b, hd69a, htr016a, htr167a, htr567a, htr569a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  rcases m.htr 6 7 9 (by decide) (by decide) with
    ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
  ·
    linarith only [hlam, hc467zy, htr347a, htr349a, htr479b, htr679a]
  ·
    linarith only [hlam, hd01b, hd79a, htr015a, htr156a, htr567a, htr679a]

theorem shard_450 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046a : m.d 0 4 + lam ≤ m.d 4 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr047b : m.d 0 4 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr145b : m.d 1 4 < m.d 1 5)
    (htr146b : m.d 1 4 < m.d 1 6)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr349a : m.d 4 9 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_450 m htr015a htr016a htr034b htr045a htr045b htr045c htr046a htr046b htr046c htr047b htr047c htr134b htr145b htr146b htr234a htr346a htr347a htr349a

#print axioms shard_450
end Jsp404.NoSatElevenDBMTerminal
