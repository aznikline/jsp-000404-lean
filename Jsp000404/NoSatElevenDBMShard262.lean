import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_262 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc126xy, hc126yx, hc126yz, hc126zy⟩ := endpoint_caps m 1 2 6 (by decide) (by decide)
  obtain ⟨hc127xy, hc127yx, hc127yz, hc127zy⟩ := endpoint_caps m 1 2 7 (by decide) (by decide)
  obtain ⟨hc128xy, hc128yx, hc128yz, hc128zy⟩ := endpoint_caps m 1 2 8 (by decide) (by decide)
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
    linarith only [hlam, htr034b, htr046a, htr346a])
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
    linarith only [hlam, hc567xy, htr134b, htr145a, htr346a, htr456b, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc456yx, htr135b, htr157a, htr345b, htr346a, htr457a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc568xy, htr134b, htr145a, htr346a, htr456b, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hc456yx, htr135b, htr158a, htr345b, htr346a, htr458a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hc569xy, htr134b, htr145a, htr346a, htr456b, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, hc456yx, htr135b, htr159a, htr345b, htr346a, htr459a])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced4510 := (m.htr 4 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4510a, htr4510b, htr4510c, _, _⟩
    linarith only [hlam, hc5610xy, htr134b, htr145a, htr346a, htr4510a, htr456b])
  obtain ⟨htr4510a, htr4510b, htr4510c, _, _⟩ := hforced4510
  have hforced1510 := (m.htr 1 5 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr1510a, htr1510b, htr1510c, _, _⟩
    linarith only [hlam, hc456yx, htr135b, htr1510a, htr345b, htr346a, htr4510a])
  obtain ⟨htr1510a, htr1510b, htr1510c, _, _⟩ := hforced1510
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hd12b, hd67a, htr012a, htr014a, htr134b, htr346a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc456yx, htr045a, htr046c, htr067a, htr467a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd12b, hd78a, htr012a, htr015a, htr157a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, hd12b, hd57a, htr012a, htr017a, htr178a, htr578a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hd12b, hd79a, htr012a, htr015a, htr157a, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr179a, htr179b, htr179c, _, _⟩
    linarith only [hlam, hd12b, hd57a, htr012a, htr017a, htr179a, htr579a])
  obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
    linarith only [hlam, hd12b, hd89a, htr012a, htr015a, htr158a, htr589a])
  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
  have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr189a, htr189b, htr189c, _, _⟩
    linarith only [hlam, hd12b, hd58a, htr012a, htr018a, htr189a, htr589a])
  obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
  have hforced5910 := (m.htr 5 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr5910a, htr5910b, htr5910c, _, _⟩
    linarith only [hlam, hd12b, hd910a, htr012a, htr015a, htr159a, htr5910a])
  obtain ⟨htr5910a, htr5910b, htr5910c, _, _⟩ := hforced5910
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc127yx, hc578yz, htr012a, htr015a, htr158a, htr179a, htr678a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr789a, htr789b, htr789c, _, _⟩
      linarith only [hlam, hc126yx, hc589yz, htr012a, htr015a, htr016b, htr067a, htr159a, htr678a, htr789a])
    obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
    have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
      linarith only [hlam, hc126yx, hc5910yz, htr012a, htr015a, htr016b, htr067a, htr1510a, htr679a, htr7910a])
    obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
    rcases m.htr 8 9 10 (by decide) (by decide) with
      ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
    ·
      linarith only [hlam, hc128yx, hc579yz, htr012a, htr015a, htr159a, htr189a, htr7910a, htr8910a]
    ·
      linarith only [hlam, hc578yz, htr589b, htr5910a, htr789a, htr8910a]
  ·
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc127yx, hc579yz, htr012a, htr015a, htr159a, htr178a, htr678a, htr679a])
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
      linarith only [hlam, hc127yx, hc5910yz, htr012a, htr015a, htr1510a, htr178a, htr789a, htr8910a]
    ·
      linarith only [hlam, hc127yx, hc589yz, htr012a, htr015a, htr159a, htr179a, htr7910a, htr8910a]

theorem shard_262 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017a : m.d 1 7 + lam ≤ m.d 0 1)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr034b : m.d 3 4 < m.d 0 4)
    (htr045a : m.d 0 4 + lam ≤ m.d 4 5)
    (htr045b : m.d 0 4 < m.d 0 5)
    (htr045c : m.d 0 5 < m.d 4 5)
    (htr134b : m.d 3 4 < m.d 1 4)
    (htr135b : m.d 3 5 < m.d 1 5)
    (htr145a : m.d 1 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_262 m htr012a htr014a htr015a htr016b htr017a htr018a htr034b htr045a htr045b htr045c htr134b htr135b htr145a htr345b htr346a

#print axioms shard_262
end Jsp404.NoSatElevenDBMTerminal
