import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_478 {lam p : ℝ} (m : ElevenModel lam p)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 1 3)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr139b : m.d 1 3 < m.d 1 9)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd34a := (m.hrange 3 4 (by decide)).1
  have hd35a := (m.hrange 3 5 (by decide)).1
  have hd36a := (m.hrange 3 6 (by decide)).1
  obtain ⟨hd49a, hd49braw⟩ := m.hrange 4 9 (by decide)
  have hd49b : m.d 4 9 < 4*lam := by
    linarith only [hd49braw, hp]
  obtain ⟨hd59a, hd59braw⟩ := m.hrange 5 9 (by decide)
  have hd59b : m.d 5 9 < 4*lam := by
    linarith only [hd59braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc367xy, hc367yx, hc367yz, hc367zy⟩ := endpoint_caps m 3 6 7 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc469xy, hc469yx, hc469yz, hc469zy⟩ := endpoint_caps m 4 6 9 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr149a, htr149b, htr149c, _, _⟩
    linarith only [hlam, htr134c, htr139b, htr149c])
  obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, htr135c, htr139b, htr159c])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, htr136c, htr139b, htr169c])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, htr137c, htr139b, htr179c])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced349 := (m.htr 3 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr349a, htr349b, htr349c, _, _⟩
    linarith only [hlam, htr134b, htr149a, htr349a])
  obtain ⟨htr349a, htr349b, htr349c, _, _⟩ := hforced349
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, hc234zy, htr134a, htr139a, htr249a, htr349c])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc459xy, htr134a, htr139a, htr345a, htr349c])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, hc469xy, htr134a, htr139a, htr346a, htr349c])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, htr135b, htr159a, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc569xy, htr135a, htr139a, htr356a, htr359c])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr369a, htr369b, htr369c, _, _⟩
    linarith only [hlam, htr136b, htr169a, htr369a])
  obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hc679xy, htr136a, htr139a, htr367a, htr369c])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
    linarith only [hlam, htr137b, htr179a, htr379a])
  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc345yz, htr135a, htr139a, htr359c, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hc346yz, htr136a, htr139a, htr369c, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hc356yz, htr136a, htr139a, htr369c, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hc367yz, htr137a, htr139a, htr379c, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  rcases m.htr 4 5 6 (by decide) (by decide) with
    ⟨htr456a, htr456b, htr456c, _, _⟩ | ⟨htr456a, htr456b, htr456c, _, _⟩
  ·
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hd12a, hd69b, htr124a, htr245a, htr456a, htr569a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd34a, hd69b, htr245a, htr246a, htr345a, htr469a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd36a, hd49b, htr246a, htr249a, htr367a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd34a, hd79b, htr345a, htr456a, htr567a, htr679a]
    ·
      linarith only [hlam, hd34a, hd69b, htr346a, htr467a, htr567a, htr569a]
  ·
    have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr245a, htr245b, htr245c, _, _⟩
      linarith only [hlam, hd35a, hd49b, htr245a, htr249a, htr356a, htr456a])
    obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
    have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr246a, htr246b, htr246c, _, _⟩
      linarith only [hlam, hd34a, hd59b, htr245a, htr246a, htr346a, htr459a])
    obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd12a, hd79b, htr124a, htr246a, htr467a, htr679a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd35a, hd69b, htr356a, htr467a, htr469a, htr567a]
    ·
      linarith only [hlam, hc345yz, htr356b, htr367a, htr456a, htr567a]

theorem shard_478 {lam p : ℝ} (m : ElevenModel lam p)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 1 3)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136b : m.d 3 6 < m.d 1 6)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr137b : m.d 3 7 < m.d 1 7)
    (htr137c : m.d 1 7 < m.d 1 3)
    (htr139a : m.d 1 3 + lam ≤ m.d 3 9)
    (htr139b : m.d 1 3 < m.d 1 9)
    : False :=
  proof_shard_478 m htr124a htr134a htr134b htr134c htr135a htr135b htr135c htr136a htr136b htr136c htr137a htr137b htr137c htr139a htr139b

#print axioms shard_478
end Jsp404.NoSatElevenDBMTerminal
