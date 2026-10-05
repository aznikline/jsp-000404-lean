import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_193 {lam p : ℝ} (m : ElevenModel lam p)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046a : m.d 0 4 + lam ≤ m.d 4 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr047b : m.d 0 4 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr3410a : m.d 4 10 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd610a := (m.hrange 6 10 (by decide)).1
  have hd710a := (m.hrange 7 10 (by decide)).1
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc4510xy, hc4510yx, hc4510yz, hc4510zy⟩ := endpoint_caps m 4 5 10 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc4610xy, hc4610yx, hc4610yz, hc4610zy⟩ := endpoint_caps m 4 6 10 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  have hforced0410 := (m.htr 0 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0410a, htr0410b, htr0410c, _, _⟩
    linarith only [hlam, htr034b, htr0410a, htr3410a])
  obtain ⟨htr0410a, htr0410b, htr0410c, _, _⟩ := hforced0410
  have hforced0510 := (m.htr 0 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0510a, htr0510b, htr0510c, _, _⟩
    linarith only [hlam, htr0410c, htr045b, htr0510b])
  obtain ⟨htr0510a, htr0510b, htr0510c, _, _⟩ := hforced0510
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, htr0410c, htr046b, htr0610b])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced0710 := (m.htr 0 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0710a, htr0710b, htr0710c, _, _⟩
    linarith only [hlam, htr0410c, htr047b, htr0710b])
  obtain ⟨htr0710a, htr0710b, htr0710c, _, _⟩ := hforced0710
  have hforced2410 := (m.htr 2 4 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2410a, htr2410b, htr2410c, _, _⟩
    linarith only [hlam, hc123zy, htr134a, htr234b, htr2410a, htr3410a])
  obtain ⟨htr2410a, htr2410b, htr2410c, _, _⟩ := hforced2410
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, htr045c, htr0510a, htr4510a])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc5610yx, htr034b, htr045a, htr3410a, htr4510b, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc4510yx, htr2410a, htr245b, htr256a, htr456a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, htr046c, htr0610a, htr4610a])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hc6710yx, htr034b, htr046a, htr3410a, htr4610b, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc4610yx, htr2410a, htr246b, htr267a, htr467a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
    linarith only [hlam, htr047c, htr0710a, htr4710a])
  obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hc456zy, htr3410a, htr346a, htr4610b, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd12b, hd610a, htr126a, htr267a, htr5610a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  rcases m.htr 6 7 10 (by decide) (by decide) with
    ⟨htr6710a, htr6710b, htr6710c, _, _⟩ | ⟨htr6710a, htr6710b, htr6710c, _, _⟩
  ·
    linarith only [hlam, hc467zy, htr3410a, htr347a, htr4710b, htr6710a]
  ·
    linarith only [hlam, hd12b, hd710a, htr125a, htr256a, htr567a, htr6710a]

theorem shard_193 {lam p : ℝ} (m : ElevenModel lam p)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr046a : m.d 0 4 + lam ≤ m.d 4 6)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr046c : m.d 0 6 < m.d 4 6)
    (htr047b : m.d 0 4 < m.d 0 7)
    (htr047c : m.d 0 7 < m.d 4 7)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr245b : m.d 2 4 < m.d 2 5)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr347a : m.d 3 4 + lam ≤ m.d 4 7)
    (htr3410a : m.d 4 10 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_193 m htr034b htr045a htr045b htr045c htr046a htr046b htr046c htr047b htr047c htr125a htr126a htr134a htr234b htr245b htr246b htr346a htr347a htr3410a

#print axioms shard_193
end Jsp404.NoSatElevenDBMTerminal
