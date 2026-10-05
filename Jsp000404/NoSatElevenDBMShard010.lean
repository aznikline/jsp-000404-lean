import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_010 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc346xy, hc346yx, hc346yz, hc346zy⟩ := endpoint_caps m 3 4 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hc023yz, htr036a, htr134a, htr136a, htr234a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr034b, htr036c, htr046b])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr035b, htr036c, htr056b])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr346a, htr346b, htr346c, _, _⟩
    linarith only [hlam, htr014c, htr046a, htr134c, htr346a])
  obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc456yx, htr013c, htr036a, htr134a, htr345a, htr346b])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, htr015c, htr056a, htr135c, htr356a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, hc567xy, htr013c, htr036a, htr135a, htr356b, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc568xy, htr013c, htr036a, htr135a, htr356b, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hd23b, hd67a, htr134a, htr136a, htr234a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc346yx, htr134a, htr136c, htr167a, htr367a])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, hd23b, hd68a, htr134a, htr136a, htr234a, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, hc346yx, htr134a, htr136c, htr168a, htr368a])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd23b, hd45a, htr134a, htr136a, htr234a, htr356b, htr456a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr235a, htr357a, htr456a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hd23b, hd56a, htr235a, htr358a, htr456a, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, htr356b, htr367a, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, htr356b, htr368a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd23b, hd78a, htr234a, htr345a, htr457a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr589a, htr589b, htr589c, _, _⟩
    linarith only [hlam, hd23b, hd89a, htr234a, htr345a, htr458a, htr589a])
  obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
  rcases m.htr 6 7 8 (by decide) (by decide) with
    ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hd01a, hd78b, htr012a, htr126a, htr267a, htr678a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd01a, hd68b, htr016a, htr167a, htr267a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hc256zy, htr268a, htr568b, htr589a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd01a, hd89b, htr016a, htr167a, htr678a, htr789a]
    ·
      linarith only [hlam, hd01a, hd78b, htr016a, htr168a, htr689a, htr789a]
  ·
    have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr267a, htr267b, htr267c, _, _⟩
      linarith only [hlam, hc256zy, htr267a, htr567b, htr578a, htr678a])
    obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
    have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr268a, htr268b, htr268c, _, _⟩
      linarith only [hlam, hd01a, hd67b, htr016a, htr168a, htr267a, htr268a])
    obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hd01a, hd89b, htr012a, htr126a, htr268a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hc567yz, htr578a, htr678c, htr689a, htr789a]
    ·
      linarith only [hlam, hc567yz, htr578b, htr589a, htr678a, htr789a]

theorem shard_010 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 0 1 + lam ≤ m.d 1 2)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016a : m.d 0 1 + lam ≤ m.d 1 6)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136a : m.d 3 6 + lam ≤ m.d 1 3)
    (htr136c : m.d 1 6 < m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_010 m htr012a htr013c htr014c htr015c htr016a htr034b htr035b htr126a htr134a htr134c htr135a htr135c htr136a htr136c htr234a htr235a

#print axioms shard_010
end Jsp404.NoSatElevenDBMTerminal
