import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_552 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc5610xy, hc5610yx, hc5610yz, hc5610zy⟩ := endpoint_caps m 5 6 10 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc579xy, hc579yx, hc579yz, hc579zy⟩ := endpoint_caps m 5 7 9 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  obtain ⟨hc5910xy, hc5910yx, hc5910yz, hc5910zy⟩ := endpoint_caps m 5 9 10 (by decide) (by decide)
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr014b, htr046a, htr134b, htr346a])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr045b, htr046c, htr056b])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, htr045c, htr056a, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc567xy, htr234b, htr245a, htr346a, htr456b, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc456yx, htr235b, htr257a, htr345b, htr346a, htr457a])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc568xy, htr234b, htr245a, htr346a, htr456b, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, hc456yx, htr235b, htr258a, htr345b, htr346a, htr458a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc569xy, htr234b, htr245a, htr346a, htr456b, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced259 := (m.htr 2 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr259a, htr259b, htr259c, _, _⟩
    linarith only [hlam, hc456yx, htr235b, htr259a, htr345b, htr346a, htr459a])
  obtain ⟨htr259a, htr259b, htr259c, _, _⟩ := hforced259
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hc5610xy, htr234b, htr245a, htr346a, htr4510a, htr456b])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced2510 := (m.htr 2 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2510a, htr2510b, htr2510c, _, _⟩
    linarith only [hlam, hc456yx, htr235b, htr2510a, htr345b, htr346a, htr4510a])
  obtain ⟨htr2510a, htr2510b, htr2510c, _, _⟩ := hforced2510
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd01b, hd67a, htr013a, htr134a, htr346a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc456yx, htr045a, htr046c, htr067a, htr467a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr278a, htr578a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hd01b, hd79a, htr012a, htr125a, htr257a, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, hd01b, hd57a, htr012a, htr127a, htr279a, htr579a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
    linarith only [hlam, hd01b, hd89a, htr012a, htr125a, htr258a, htr589a])
  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
  have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr289a, htr289b, htr289c, _, _⟩
    linarith only [hlam, hd01b, hd58a, htr012a, htr128a, htr289a, htr589a])
  obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
    linarith only [hlam, hd01b, hd910a, htr012a, htr125a, htr259a, htr5910a])
  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc237yx, hc578yz, htr123a, htr125a, htr258a, htr279a, htr678a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, hc016yx, hc589yz, htr012a, htr067a, htr125a, htr259a, htr678a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hc016yx, hc5910yz, htr012a, htr067a, htr125a, htr2510a, htr679a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      linarith only [hlam, hc238yx, hc579yz, htr123a, htr125a, htr259a, htr289a, htr7910a, htr8910a]
    ·
      linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]
  ·
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc237yx, hc579yz, htr123a, htr125a, htr259a, htr278a, htr678a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hc567yz, htr579b, htr5910a, htr679a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      linarith only [hlam, hc237yx, hc5910yz, htr123a, htr125a, htr2510a, htr278a, htr789a, htr8910a]
    ·
      linarith only [hlam, hc237yx, hc589yz, htr123a, htr125a, htr259a, htr279a, htr7910a, htr8910a]

theorem shard_552 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_552 m htr012a htr013a htr014b htr045a htr045b htr045c htr123a htr125a htr127a htr128a htr134a htr134b htr234b htr235b htr245a htr345b htr346a

#print axioms shard_552
end Jsp404.NoSatElevenDBMTerminal
