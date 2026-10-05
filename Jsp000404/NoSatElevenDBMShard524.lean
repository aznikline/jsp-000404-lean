import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_524 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc569xy, hc569yx, hc569yz, hc569zy⟩ := endpoint_caps m 5 6 9 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc589xy, hc589yx, hc589yz, hc589zy⟩ := endpoint_caps m 5 8 9 (by decide) (by decide)
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, htr024a, htr026a, htr234b, htr236c])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, htr023b, htr036a, htr236a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr034b, htr036c, htr046b])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr035b, htr036c, htr056b])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, hc346yx, htr123a, htr126a, htr234a, htr236b])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, hc012zy, htr023a, htr123b, htr136a, htr236a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, htr034c, htr046a, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc456yx, htr023b, htr034a, htr236a, htr345a, htr346b])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc346yx, htr134b, htr136a, htr145a, htr345a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr035c, htr056a, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc567xy, htr023b, htr035a, htr236a, htr356b, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced157 := (m.htr 1 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr157a, htr157b, htr157c, _, _⟩
    linarith only [hlam, hc356yx, htr135b, htr136a, htr157a, htr357a])
  obtain ⟨htr157a, htr157b, htr157c, _, _⟩ := hforced157
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc568xy, htr023b, htr035a, htr236a, htr356b, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced158 := (m.htr 1 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr158a, htr158b, htr158c, _, _⟩
    linarith only [hlam, hc356yx, htr135b, htr136a, htr158a, htr358a])
  obtain ⟨htr158a, htr158b, htr158c, _, _⟩ := hforced158
  have hforced359 := (m.htr 3 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr359a, htr359b, htr359c, _, _⟩
    linarith only [hlam, hc569xy, htr023b, htr035a, htr236a, htr356b, htr359a])
  obtain ⟨htr359a, htr359b, htr359c, _, _⟩ := hforced359
  have hforced159 := (m.htr 1 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr159a, htr159b, htr159c, _, _⟩
    linarith only [hlam, hc356yx, htr135b, htr136a, htr159a, htr359a])
  obtain ⟨htr159a, htr159b, htr159c, _, _⟩ := hforced159
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc345zy, htr235a, htr236a, htr356b, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr015a, htr157a, htr456a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr015a, htr158a, htr456a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced459 := (m.htr 4 5 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr459a, htr459b, htr459c, _, _⟩
    linarith only [hlam, hd01b, hd56a, htr015a, htr159a, htr456a, htr459a])
  obtain ⟨htr459a, htr459b, htr459c, _, _⟩ := hforced459
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hd01b, hd67a, htr014a, htr145a, htr456a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd02b, hd56a, htr023a, htr236a, htr367a, htr567a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc346yx, htr034a, htr036c, htr067a, htr367a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd01b, hd68a, htr014a, htr145a, htr456a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd02b, hd56a, htr023a, htr236a, htr368a, htr568a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, hc346yx, htr034a, htr036c, htr068a, htr368a])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd01b, hd78a, htr014a, htr145a, htr457a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
    linarith only [hlam, hd01b, hd89a, htr014a, htr145a, htr458a, htr589a])
  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hc012zy, hc578yz, htr024a, htr026b, htr067a, htr124c, htr126a, htr145a, htr458a, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
    linarith only [hlam, hc012zy, hc589yz, htr024a, htr026b, htr068a, htr124c, htr126a, htr145a, htr459a, htr689a])
  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
  rcases m.htr 7 8 9 (by decide) (by decide) with
    ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
  ·
    linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
  ·
    linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]

theorem shard_524 {lam p : ℝ} (m : ElevenModel lam p)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr034a : m.d 0 3 + lam ≤ m.d 3 4)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr034c : m.d 0 4 < m.d 3 4)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr236c : m.d 2 6 < m.d 2 3)
    : False :=
  proof_shard_524 m htr014a htr015a htr023a htr023b htr024a htr034a htr034b htr034c htr035a htr035b htr035c htr123a htr123b htr124c htr134b htr135b htr234a htr234b htr235a htr236a htr236b htr236c

#print axioms shard_524
end Jsp404.NoSatElevenDBMTerminal
