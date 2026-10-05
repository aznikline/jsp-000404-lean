import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_027 {lam p : ℝ} (m : ElevenModel lam p)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127b : m.d 1 2 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr129c : m.d 1 9 < m.d 1 2)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
  have hd59a := (m.hrange 5 9 (by decide)).1
  have hd69a := (m.hrange 6 9 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc349xy, hc349yx, hc349yz, hc349zy⟩ := endpoint_caps m 3 4 9 (by decide) (by decide)
  obtain ⟨hc459xy, hc459yx, hc459yz, hc459zy⟩ := endpoint_caps m 4 5 9 (by decide) (by decide)
  obtain ⟨hc469xy, hc469yx, hc469yz, hc469zy⟩ := endpoint_caps m 4 6 9 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  have hforced139 := (m.htr 1 3 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr139a, htr139b, htr139c, _, _⟩
    linarith only [hlam, htr123b, htr129c, htr139b])
  obtain ⟨htr139a, htr139b, htr139c, _, _⟩ := hforced139
  have hforced149 := (m.htr 1 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr149a, htr149b, htr149c, _, _⟩
    linarith only [hlam, htr124b, htr129c, htr149b])
  obtain ⟨htr149a, htr149b, htr149c, _, _⟩ := hforced149
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, htr125b, htr129c, htr159b])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced169 := (m.htr 1 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr169a, htr169b, htr169c, _, _⟩
    linarith only [hlam, htr126b, htr129c, htr169b])
  obtain ⟨htr169a, htr169b, htr169c, _, _⟩ := hforced169
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, htr127b, htr129c, htr179b])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced239 := (m.htr 2 3 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr239a, htr239b, htr239c, _, _⟩
    linarith only [hlam, htr123c, htr139a, htr239a])
  obtain ⟨htr239a, htr239b, htr239c, _, _⟩ := hforced239
  have hforced234 := (m.htr 2 3 4 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr234a, htr234b, htr234c, _, _⟩
    linarith only [hlam, hc349yx, htr123a, htr129a, htr234a, htr239b])
  obtain ⟨htr234a, htr234b, htr234c, _, _⟩ := hforced234
  have hforced249 := (m.htr 2 4 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr249a, htr249b, htr249c, _, _⟩
    linarith only [hlam, htr124c, htr149a, htr249a])
  obtain ⟨htr249a, htr249b, htr249c, _, _⟩ := hforced249
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, hc459yx, htr124a, htr129a, htr245a, htr249b])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, hc469yx, htr124a, htr129a, htr246a, htr249b])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, htr125c, htr159a, htr259a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc569yx, htr125a, htr129a, htr256a, htr259b])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, htr126c, htr169a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc679yx, htr126a, htr129a, htr267a, htr269b])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, htr127c, htr179a, htr279a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc245zy, htr125a, htr129a, htr259b, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hc246zy, htr126a, htr129a, htr269b, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hc256zy, htr126a, htr129a, htr269b, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hc267zy, htr127a, htr129a, htr279b, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  rcases m.htr 3 4 5 (by decide) (by decide) with
    ⟨htr345a, htr345b, htr345c, _, _⟩ | ⟨htr345a, htr345b, htr345c, _, _⟩
  ·
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd24b, hd69a, htr245a, htr345a, htr346a, htr469a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hc234zy, htr245c, htr256a, htr345a, htr456a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc234zy, htr246c, htr267a, htr346a, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hd24b, hd69a, htr246a, htr467a, htr567a, htr569a]
    ·
      linarith only [hlam, hd24b, hd79a, htr245a, htr456a, htr567a, htr679a]
  ·
    have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr346a, htr346b, htr346c, _, _⟩
      linarith only [hlam, hd24b, hd59a, htr246a, htr345a, htr346a, htr459a])
    obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
    have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr456a, htr456b, htr456c, _, _⟩
      linarith only [hlam, hd23b, hd69a, htr234a, htr345a, htr456a, htr569a])
    obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hd23b, hd79a, htr234a, htr346a, htr467a, htr679a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 5 6 7 (by decide) (by decide) with
      ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
    ·
      linarith only [hlam, hc245zy, htr256c, htr267a, htr456a, htr567a]
    ·
      linarith only [hlam, hd25b, hd69a, htr256a, htr467a, htr469a, htr567a]

theorem shard_027 {lam p : ℝ} (m : ElevenModel lam p)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126b : m.d 1 2 < m.d 1 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127b : m.d 1 2 < m.d 1 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr129a : m.d 2 9 + lam ≤ m.d 1 2)
    (htr129c : m.d 1 9 < m.d 1 2)
    : False :=
  proof_shard_027 m htr123a htr123b htr123c htr124a htr124b htr124c htr125a htr125b htr125c htr126a htr126b htr126c htr127a htr127b htr127c htr129a htr129c

#print axioms shard_027
end Jsp404.NoSatElevenDBMTerminal
