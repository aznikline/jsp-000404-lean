import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_146 {lam p : ℝ} (m : ElevenModel lam p)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr138c : m.d 1 8 < m.d 1 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < 4*lam := by
    linarith only [hd34braw, hp]
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd36a, hd36braw⟩ := m.hrange 3 6 (by decide)
  have hd36b : m.d 3 6 < 4*lam := by
    linarith only [hd36braw, hp]
  have hd48a := (m.hrange 4 8 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, htr134b, htr138c, htr148b])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, htr135b, htr138c, htr158b])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, htr136b, htr138c, htr168b])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, htr137b, htr138c, htr178b])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, htr134c, htr148a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, hc234yz, htr134a, htr138a, htr248a, htr348b])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc458yx, htr134a, htr138a, htr345a, htr348b])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hc468yx, htr134a, htr138a, htr346a, htr348b])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, htr135c, htr158a, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc568yx, htr135a, htr138a, htr356a, htr358b])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, htr136c, htr168a, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hc678yx, htr136a, htr138a, htr367a, htr368b])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, htr137c, htr178a, htr378a])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc345zy, htr135a, htr138a, htr358b, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hc346zy, htr136a, htr138a, htr368b, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc356zy, htr136a, htr138a, htr368b, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hc367zy, htr137a, htr138a, htr378b, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  rcases m.htr 4 5 6 (by decide) (by decide) with
    ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
  ·
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hd35b, hd48a, htr245a, htr248a, htr356a, htr456a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd34b, hd58a, htr245a, htr246a, htr346a, htr458a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd12b, hd78a, htr124a, htr246a, htr467a, htr678a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hc345zy, htr356c, htr367a, htr456a, htr567a]
    ·
      linarith only [hlam, hd35b, hd68a, htr356a, htr467a, htr468a, htr567a]
  ·
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hd12b, hd68a, htr124a, htr245a, htr456a, htr568a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd34b, hd68a, htr245a, htr246a, htr345a, htr468a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd36b, hd48a, htr246a, htr248a, htr367a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd34b, hd68a, htr346a, htr467a, htr567a, htr568a]
    ·
      linarith only [hlam, hd34b, hd78a, htr345a, htr456a, htr567a, htr678a]

theorem shard_146 {lam p : ℝ} (m : ElevenModel lam p)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 1 3 + lam ≤ m.d 3 6)
    (htr136b : m.d 1 3 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 1 3 + lam ≤ m.d 3 7)
    (htr137b : m.d 1 3 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 3 7)
    (htr138a : m.d 3 8 + lam ≤ m.d 1 3)
    (htr138c : m.d 1 8 < m.d 1 3)
    : False :=
  proof_shard_146 m htr124a htr134a htr134b htr134c htr135a htr135b htr135c htr136a htr136b htr136c htr137a htr137b htr137c htr138a htr138c

#print axioms shard_146
end Jsp404.NoSatElevenDBMTerminal
