import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_422 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc123xy, hc123yx, hc123yz, hc123zy⟩ := endpoint_caps m 1 2 3 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc467xy, hc467yx, hc467yz, hc467zy⟩ := endpoint_caps m 4 6 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc457yx, htr034a, htr037a, htr345a, htr347b])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hc123yz, htr014b, htr047a, htr134b, htr234a, htr347a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr045b, htr047c, htr057b])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr046b, htr047c, htr067b])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, htr235a, htr237a, htr345b, htr347c])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, htr234b, htr247a, htr347a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, htr035c, htr057a, htr345c, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc567yx, htr234b, htr245a, htr347a, htr456a, htr457b])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc457yx, htr045b, htr047a, htr056a, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, htr036c, htr067a, htr346c, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hc678xy, htr234b, htr246a, htr347a, htr467b, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, hc467yx, htr046b, htr047a, htr068a, htr468a])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hc679xy, htr234b, htr246a, htr347a, htr467b, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced069 := (m.htr 0 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr069a, htr069b, htr069c, _, _⟩
    linarith only [hlam, hc467yx, htr046b, htr047a, htr069a, htr469a])
  obtain ⟨htr069a, htr069b, htr069c, _, _⟩ := hforced069
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hc6710xy, htr234b, htr246a, htr347a, htr4610a, htr467b])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced0610 := (m.htr 0 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr0610a, htr0610b, htr0610c, _, _⟩
    linarith only [hlam, hc467yx, htr046b, htr047a, htr0610a, htr4610a])
  obtain ⟨htr0610a, htr0610b, htr0610c, _, _⟩ := hforced0610
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hc456zy, htr346a, htr347a, htr467b, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd23b, hd67a, htr036c, htr068a, htr236a, htr567a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hd23b, hd67a, htr036c, htr069a, htr236a, htr567a, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hd23b, hd67a, htr036c, htr0610a, htr236a, htr5610a, htr567a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hd23b, hd78a, htr035c, htr056a, htr235a, htr567a, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hd23b, hd67a, htr234a, htr347a, htr478a, htr678a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, hc457yx, htr245a, htr247c, htr278a, htr478a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr679a, htr679b, htr679c, _, _⟩
    linarith only [hlam, hd23b, hd79a, htr035c, htr056a, htr235a, htr567a, htr679a])
  obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
    linarith only [hlam, hd23b, hd67a, htr234a, htr347a, htr479a, htr679a])
  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, hc457yx, htr245a, htr247c, htr279a, htr479a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
    linarith only [hlam, hd23b, hd89a, htr035c, htr056a, htr235a, htr568a, htr689a])
  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
    linarith only [hlam, hd23b, hd910a, htr035c, htr056a, htr235a, htr569a, htr6910a])
  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
    linarith only [hlam, hc023yz, hc689yz, htr035c, htr037a, htr056a, htr235a, htr237b, htr278a, htr569a, htr789a])
  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
    linarith only [hlam, hc023yz, hc6910yz, htr035c, htr037a, htr056a, htr235a, htr237b, htr279a, htr5610a, htr7910a])
  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
  rcases m.htr 8 9 10 (by decide) (by decide) with
    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
  ·
    linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
  ·
    linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]

theorem shard_422 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014b : m.d 1 4 < m.d 0 4)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr046b : m.d 0 4 < m.d 0 6)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr234b : m.d 3 4 < m.d 2 4)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr245a : m.d 2 4 + lam ≤ m.d 4 5)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    : False :=
  proof_shard_422 m htr014b htr034a htr035c htr036c htr045b htr046b htr134b htr234a htr234b htr235a htr236a htr245a htr246a htr345a htr345b htr345c htr346a htr346c htr347a htr347b htr347c

#print axioms shard_422
end Jsp404.NoSatElevenDBMTerminal
