import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_257 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd14a := (m.hrange 1 4 (by decide)).1
  have hd15a := (m.hrange 1 5 (by decide)).1
  have hd16a := (m.hrange 1 6 (by decide)).1
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hc145xy, hc145yx, hc145yz, hc145zy⟩ := endpoint_caps m 1 4 5 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc157xy, hc157yx, hc157yz, hc157zy⟩ := endpoint_caps m 1 5 7 (by decide) (by decide)
  obtain ⟨hc167xy, hc167yx, hc167yz, hc167zy⟩ := endpoint_caps m 1 6 7 (by decide) (by decide)
  obtain ⟨hc178xy, hc178yx, hc178yz, hc178zy⟩ := endpoint_caps m 1 7 8 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr049a, htr049b, htr049c, _, _⟩
    linarith only [hlam, htr014c, htr019b, htr049c])
  obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
  have hforced059 := (m.htr 0 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr059a, htr059b, htr059c, _, _⟩
    linarith only [hlam, htr015c, htr019b, htr059c])
  obtain ⟨htr059a, htr059b, htr059c, _, _⟩ := hforced059
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, htr016c, htr019b, htr069c])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr079a, htr079b, htr079c, _, _⟩
    linarith only [hlam, htr017c, htr019b, htr079c])
  obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
  have hforced089 := (m.htr 0 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr089a, htr089b, htr089c, _, _⟩
    linarith only [hlam, htr018c, htr019b, htr089c])
  obtain ⟨htr089a, htr089b, htr089c, _, _⟩ := hforced089
  have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr149a, htr149b, htr149c, _, _⟩
    linarith only [hlam, htr014b, htr049a, htr149a])
  obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc459xy, htr014a, htr019a, htr145a, htr149c])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, htr015b, htr059a, htr159a])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, hc569xy, htr015a, htr019a, htr156a, htr159c])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc579xy, htr015a, htr019a, htr157a, htr159c])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, htr016b, htr069a, htr169a])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc679xy, htr016a, htr019a, htr167a, htr169c])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, htr017b, htr079a, htr179a])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hc789xy, htr017a, htr019a, htr178a, htr179c])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
    linarith only [hlam, htr018b, htr089a, htr189a])
  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hc156yz, htr016a, htr019a, htr169c, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hc157yz, htr017a, htr019a, htr179c, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hc167yz, htr017a, htr019a, htr179c, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
    linarith only [hlam, hc178yz, htr018a, htr019a, htr189c, htr789a])
  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
  rcases m.htr 4 5 6 (by decide) (by decide) with
    ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
  ·
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hd15a, hd69b, htr157a, htr456a, htr457a, htr569a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hd14a, hd79b, htr145a, htr456a, htr567a, htr679a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hd14a, hd89b, htr145a, htr457a, htr578a, htr789a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd16a, hd79b, htr167a, htr578a, htr579a, htr678a]
    ·
      linarith only [hlam, hc156yz, htr167b, htr178a, htr567a, htr678a]
  ·
    have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr457a, htr457b, htr457c, _, _⟩
      linarith only [hlam, hd15a, hd79b, htr156a, htr456a, htr457a, htr579a])
    obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
    have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr567a, htr567b, htr567c, _, _⟩
      linarith only [hlam, hc145yz, htr156b, htr167a, htr456a, htr567a])
    obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc145yz, htr157b, htr178a, htr457a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    rcases m.htr 6 7 8 (by decide) (by decide) with
      ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
    ·
      linarith only [hlam, hd15a, hd89b, htr156a, htr567a, htr678a, htr789a]
    ·
      linarith only [hlam, hd15a, hd79b, htr157a, htr578a, htr678a, htr679a]

theorem shard_257 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr014c : m.d 0 4 < m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr015c : m.d 0 5 < m.d 0 1)
    (htr016a : m.d 1 6 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr016c : m.d 0 6 < m.d 0 1)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr017c : m.d 0 7 < m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr018b : m.d 1 8 < m.d 0 8)
    (htr018c : m.d 0 8 < m.d 0 1)
    (htr019a : m.d 0 1 + lam ≤ m.d 1 9)
    (htr019b : m.d 0 1 < m.d 0 9)
    : False :=
  proof_shard_257 m htr014a htr014b htr014c htr015a htr015b htr015c htr016a htr016b htr016c htr017a htr017b htr017c htr018a htr018b htr018c htr019a htr019b

#print axioms shard_257
end Jsp404.NoSatElevenDBMTerminal
