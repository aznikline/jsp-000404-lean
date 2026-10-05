import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_172 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, htr034c, htr048a, htr348a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr045c, htr048b, htr058c])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr046c, htr048b, htr068c])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, htr047c, htr048b, htr078c])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, hc123zy, htr134c, htr148a, htr234a, htr348a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, htr045b, htr058a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc568xy, htr034c, htr045a, htr348a, htr456a, htr458c])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc458xy, htr145c, htr148a, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
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
    linarith only [hlam, hc468xy, htr146c, htr148a, htr167a, htr467a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, htr047b, htr078a, htr478a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc456yz, htr346a, htr348a, htr468c, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd01a, hd68b, htr016a, htr167a, htr567a, htr568a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    linarith only [hlam, hd01a, hd78b, htr015a, htr156a, htr567a, htr678a]
  ·
    linarith only [hlam, hc467yz, htr347a, htr348a, htr478c, htr678a]

theorem shard_172 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr045a : m.d 4 5 + lam ≤ m.d 0 4)
    (htr045b : m.d 4 5 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 0 4)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr046b : m.d 4 6 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 0 4)
    (htr047b : m.d 4 7 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 0 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr145c : m.d 1 5 < m.d 1 4)
    (htr146c : m.d 1 6 < m.d 1 4)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr348a : m.d 3 4 + lam ≤ m.d 4 8)
    : False :=
  proof_shard_172 m htr015a htr016a htr034c htr045a htr045b htr045c htr046a htr046b htr046c htr047b htr047c htr134c htr145c htr146c htr234a htr346a htr347a htr348a

#print axioms shard_172
end Jsp404.NoSatElevenDBMTerminal
