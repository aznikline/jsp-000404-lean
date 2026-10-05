import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_038 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr048a : m.d 4 8 + lam ≤ m.d 0 4)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd01a := (m.hrange 0 1 (by decide)).1
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd24a, hd24braw⟩ := m.hrange 2 4 (by decide)
  have hd24b : m.d 2 4 < 4*lam := by
    linarith only [hd24braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd47a := (m.hrange 4 7 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  have hd79a := (m.hrange 7 9 (by decide)).1
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc014xy, hc014yx, hc014yz, hc014zy⟩ := endpoint_caps m 0 1 4 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, hc235yx, htr025a, htr027a, htr123a, htr127a])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr026b, htr027c, htr067b])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, htr016c, htr067a, htr126c, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hc678xy, htr012c, htr027a, htr126a, htr267b, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, hc256xy, htr025a, htr026b, htr068a, htr268a])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc234zy, htr124a, htr127a, htr247b, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, hc246zy, htr126a, htr127a, htr267b, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  rcases m.htr 3 4 6 (by decide) (by decide) with
    ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
  ·
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc234zy, htr246c, htr268a, htr346a, htr468a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr478a, htr478b, htr478c, _, _⟩
      linarith only [hlam, hd24b, hd78a, htr246a, htr346a, htr347a, htr478a])
    obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd23b, hd47a, htr123a, htr127a, htr278a, htr478a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc237yx, htr123a, htr127c, htr178a, htr278a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr479a, htr479b, htr479c, _, _⟩
      linarith only [hlam, hd24b, hd79a, htr246a, htr346a, htr347a, htr479a])
    obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd23b, hd47a, htr123a, htr127a, htr279a, htr479a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hc237yx, htr123a, htr127c, htr179a, htr279a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc014xy, hc457yz, htr017a, htr046a, htr178a, htr346a, htr347a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, hc014xy, hc478yz, htr015a, htr046a, htr157a, htr346a, htr348a, htr578a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hc014xy, hc457yz, htr017a, htr046a, htr179a, htr346a, htr347a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hc014xy, hc789zy, htr015a, htr046a, htr157a, htr468a, htr579a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc014xy, hc678yz, htr015a, htr048a, htr157a, htr489a, htr578a, htr689a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd01a, hd89b, htr015a, htr157a, htr578a, htr789a]
    ·
      linarith only [hlam, hd45a, hd78b, htr345a, htr348a, htr489a, htr789a]
  ·
    have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr348a, htr348b, htr348c, _, _⟩
      linarith only [hlam, hd24b, hd67a, htr248a, htr346a, htr348a, htr467a])
    obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
    have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr678a, htr678b, htr678c, _, _⟩
      linarith only [hlam, hd23b, hd78a, htr234a, htr346a, htr467a, htr678a])
    obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd23b, hd67a, htr123a, htr127a, htr278a, htr678a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr178a, htr178b, htr178c, _, _⟩
      linarith only [hlam, hc237yx, htr123a, htr127c, htr178a, htr278a])
    obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
    have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr578a, htr578b, htr578c, _, _⟩
      linarith only [hlam, hc013xy, hc567zy, htr017a, htr034a, htr178a, htr346a, htr467a, htr578a])
    obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
    have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr468a, htr468b, htr468c, _, _⟩
      linarith only [hlam, hc013xy, hc678yz, htr015a, htr034a, htr157a, htr346a, htr468a, htr578a])
    obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
    have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr028a, htr028b, htr028c, _, _⟩
      linarith only [hlam, hc246zy, htr012c, htr028a, htr126a, htr268b, htr468a])
    obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hc789yx, htr027a, htr028a, htr278c, htr279a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced179 := (m.htr 1 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr179a, htr179b, htr179c, _, _⟩
      linarith only [hlam, hc237yx, htr123a, htr127c, htr179a, htr279a])
    obtain ⟨htr179a, htr179b, htr179c, _, _⟩ := hforced179
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hc013xy, hc567zy, htr017a, htr034a, htr179a, htr346a, htr467a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc013xy, hc789zy, htr015a, htr034a, htr157a, htr348a, htr489a, htr579a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr689a, htr689b, htr689c, _, _⟩
      linarith only [hlam, hc016xy, hc478yz, htr015a, htr068a, htr157a, htr489a, htr578a, htr689a])
    obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd01a, hd89b, htr015a, htr157a, htr578a, htr789a]
    ·
      linarith only [hlam, hd67a, hd78b, htr467a, htr468a, htr689a, htr789a]

theorem shard_038 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr015a : m.d 0 1 + lam ≤ m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017a : m.d 0 1 + lam ≤ m.d 1 7)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr034a : m.d 3 4 + lam ≤ m.d 0 3)
    (htr046a : m.d 4 6 + lam ≤ m.d 0 4)
    (htr048a : m.d 4 8 + lam ≤ m.d 0 4)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127c : m.d 1 7 < m.d 1 2)
    (htr157a : m.d 1 5 + lam ≤ m.d 5 7)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr246a : m.d 4 6 + lam ≤ m.d 2 4)
    (htr246c : m.d 2 6 < m.d 2 4)
    (htr247b : m.d 4 7 < m.d 2 7)
    (htr248a : m.d 4 8 + lam ≤ m.d 2 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    : False :=
  proof_shard_038 m htr012c htr015a htr016c htr017a htr025a htr026b htr034a htr046a htr048a htr123a htr124a htr126a htr126c htr127a htr127c htr157a htr234a htr246a htr246c htr247b htr248a htr345a

#print axioms shard_038
end Jsp404.NoSatElevenDBMTerminal
