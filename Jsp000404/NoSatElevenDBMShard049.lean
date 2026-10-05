import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_049 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  obtain ⟨hd25a, hd25braw⟩ := m.hrange 2 5 (by decide)
  have hd25b : m.d 2 5 < 4*lam := by
    linarith only [hd25braw, hp]
  obtain ⟨hd26a, hd26braw⟩ := m.hrange 2 6 (by decide)
  have hd26b : m.d 2 6 < 4*lam := by
    linarith only [hd26braw, hp]
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc015xy, hc015yx, hc015yz, hc015zy⟩ := endpoint_caps m 0 1 5 (by decide) (by decide)
  obtain ⟨hc016xy, hc016yx, hc016yz, hc016zy⟩ := endpoint_caps m 0 1 6 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc235xy, hc235yx, hc235yz, hc235zy⟩ := endpoint_caps m 2 3 5 (by decide) (by decide)
  obtain ⟨hc238xy, hc238yx, hc238yz, hc238zy⟩ := endpoint_caps m 2 3 8 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc257xy, hc257yx, hc257yz, hc257zy⟩ := endpoint_caps m 2 5 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc468xy, hc468yx, hc468yz, hc468zy⟩ := endpoint_caps m 4 6 8 (by decide) (by decide)
  obtain ⟨hc478xy, hc478yx, hc478yz, hc478zy⟩ := endpoint_caps m 4 7 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hc234yx, htr024a, htr028a, htr123a, htr128a])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr025b, htr028c, htr058b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr026b, htr028c, htr068b])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, htr027b, htr028c, htr078b])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr015c, htr058a, htr125c, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc568yx, htr012c, htr028a, htr125a, htr256a, htr258b])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc245xy, htr024a, htr025b, htr056a, htr256a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc578yx, htr012c, htr028a, htr125a, htr257a, htr258b])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, htr016c, htr068a, htr126c, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc678yx, htr012c, htr028a, htr126a, htr267a, htr268b])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc246xy, htr024a, htr026b, htr067a, htr267a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, htr017c, htr078a, htr127c, htr278a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, hc789xy, htr012c, htr028a, htr127a, htr278b, htr279a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc235zy, htr125a, htr128a, htr258b, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc256zy, htr126a, htr128a, htr268b, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hc257zy, htr127a, htr128a, htr278b, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hc267zy, htr127a, htr128a, htr278b, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc235zy, htr256c, htr267a, htr356a, htr567a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd25b, hd68a, htr257a, htr356a, htr357a, htr568a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc256zy, htr267c, htr279a, htr567a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd26b, hd78a, htr267a, htr578a, htr579a, htr679a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc013xy, hc789yz, htr014a, htr035a, htr148a, htr357a, htr489a, htr579a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hc016xy, hc468zy, htr018a, htr067a, htr189a, htr489a, htr567a, htr568a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hc238yx, htr123a, htr128c, htr189a, htr289a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd23b, hd78a, htr123a, htr128a, htr289a, htr789a]
    ·
      linarith only [hlam, hd26b, hd89a, htr267a, htr567a, htr568a, htr678b, htr789a]
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd23b, hd78a, htr235a, htr356a, htr567a, htr678a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd25b, hd78a, htr256a, htr356a, htr357a, htr578a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hc235zy, htr257c, htr279a, htr357a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd25b, hd89a, htr256a, htr356a, htr358a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hd23b, hd58a, htr123a, htr128a, htr289a, htr589a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hc238yx, htr123a, htr128c, htr189a, htr289a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc015xy, hc478zy, htr018a, htr056a, htr189a, htr489a, htr567a, htr678a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    rcases m.htr 6 7 9 (by decide) (by decide) with
      ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
    ·
      linarith only [hlam, hd25b, hd78a, htr257a, htr579a, htr678a, htr679a]
    ·
      linarith only [hlam, hc015xy, hc789yz, htr014a, htr056a, htr148a, htr489a, htr567a, htr679a]

theorem shard_049 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012c : m.d 0 2 < m.d 1 2)
    (htr014a : m.d 0 1 + lam ≤ m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr017c : m.d 0 7 < m.d 1 7)
    (htr018a : m.d 0 1 + lam ≤ m.d 1 8)
    (htr024a : m.d 2 4 + lam ≤ m.d 0 2)
    (htr025b : m.d 0 2 < m.d 0 5)
    (htr026b : m.d 0 2 < m.d 0 6)
    (htr027b : m.d 0 2 < m.d 0 7)
    (htr035a : m.d 3 5 + lam ≤ m.d 0 3)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr126a : m.d 1 2 + lam ≤ m.d 2 6)
    (htr126c : m.d 1 6 < m.d 2 6)
    (htr127a : m.d 1 2 + lam ≤ m.d 2 7)
    (htr127c : m.d 1 7 < m.d 2 7)
    (htr128a : m.d 2 8 + lam ≤ m.d 1 2)
    (htr128c : m.d 1 8 < m.d 1 2)
    (htr148a : m.d 1 4 + lam ≤ m.d 4 8)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_049 m htr012c htr014a htr015c htr016c htr017c htr018a htr024a htr025b htr026b htr027b htr035a htr123a htr125a htr125c htr126a htr126c htr127a htr127c htr128a htr128c htr148a htr235a

#print axioms shard_049
end Jsp404.NoSatElevenDBMTerminal
