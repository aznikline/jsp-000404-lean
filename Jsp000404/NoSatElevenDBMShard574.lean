import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_574 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd25a := (m.hrange 2 5 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  obtain ⟨hd58a, hd58braw⟩ := m.hrange 5 8 (by decide)
  have hd58b : m.d 5 8 < 4*lam := by
    linarith only [hd58braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
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
  have hforced028 := (m.htr 0 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr028a, htr028b, htr028c, _, _⟩
    linarith only [hlam, hc234xy, htr024a, htr028a, htr123a, htr128a])
  obtain ⟨htr028a, htr028b, htr028c, _, _⟩ := hforced028
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr025c, htr028b, htr058c])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr026c, htr028b, htr068c])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, htr027c, htr028b, htr078c])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced258 := (m.htr 2 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr258a, htr258b, htr258c, _, _⟩
    linarith only [hlam, htr015b, htr058a, htr125b, htr258a])
  obtain ⟨htr258a, htr258b, htr258c, _, _⟩ := hforced258
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hc568xy, htr012b, htr028a, htr125a, htr256a, htr258c])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc245yx, htr024a, htr025c, htr056a, htr256a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc578xy, htr012b, htr028a, htr125a, htr257a, htr258c])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, htr016b, htr068a, htr126b, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc678xy, htr012b, htr028a, htr126a, htr267a, htr268c])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc246yx, htr024a, htr026c, htr067a, htr267a])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, htr017b, htr078a, htr127b, htr278a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr279a, htr279b, htr279c, _, _⟩
    linarith only [hlam, hc789yx, htr012b, htr028a, htr127a, htr278c, htr279a])
  obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc235yz, htr125a, htr128a, htr258c, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hc256yz, htr126a, htr128a, htr268c, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hc257yz, htr127a, htr128a, htr278c, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr678a, htr678b, htr678c, _, _⟩
    linarith only [hlam, hc267yz, htr127a, htr128a, htr278c, htr678a])
  obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hd23a, hd78b, htr235a, htr356a, htr567a, htr678a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd25a, hd78b, htr256a, htr356a, htr357a, htr578a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hc235yz, htr257b, htr279a, htr357a, htr579a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr589a, htr589b, htr589c, _, _⟩
      linarith only [hlam, hd25a, hd89b, htr256a, htr356a, htr358a, htr589a])
    obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hd23a, hd58b, htr123a, htr128a, htr289a, htr589a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hc238xy, htr123a, htr128b, htr189a, htr289a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc015yx, hc478yz, htr018a, htr056a, htr189a, htr489a, htr567a, htr678a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    rcases m.htr 6 7 9 (by decide) (by decide) with
      ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
    ·
      linarith only [hlam, hc015yx, hc789zy, htr014a, htr056a, htr148a, htr489a, htr567a, htr679a]
    ·
      linarith only [hlam, hd25a, hd78b, htr257a, htr579a, htr678a, htr679a]
  ·
    have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr356a, htr356b, htr356c, _, _⟩
      linarith only [hlam, hc235yz, htr256b, htr267a, htr356a, htr567a])
    obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
    have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr357a, htr357b, htr357c, _, _⟩
      linarith only [hlam, hd25a, hd68b, htr257a, htr356a, htr357a, htr568a])
    obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
    have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr679a, htr679b, htr679c, _, _⟩
      linarith only [hlam, hc256yz, htr267b, htr279a, htr567a, htr679a])
    obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
    have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr579a, htr579b, htr579c, _, _⟩
      linarith only [hlam, hd26a, hd78b, htr267a, htr578a, htr579a, htr679a])
    obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
    have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr489a, htr489b, htr489c, _, _⟩
      linarith only [hlam, hc013yx, hc789zy, htr014a, htr035a, htr148a, htr357a, htr489a, htr579a])
    obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
    have hforced189 := (m.htr 1 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr189a, htr189b, htr189c, _, _⟩
      linarith only [hlam, hc016yx, hc468yz, htr018a, htr067a, htr189a, htr489a, htr567a, htr568a])
    obtain ⟨htr189a, htr189b, htr189c, _, _⟩ := hforced189
    have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr289a, htr289b, htr289c, _, _⟩
      linarith only [hlam, hc238xy, htr123a, htr128b, htr189a, htr289a])
    obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
    rcases m.htr 7 8 9 (by decide) (by decide) with
      ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
    ·
      linarith only [hlam, hd26a, hd89b, htr267a, htr567a, htr568a, htr678c, htr789a]
    ·
      linarith only [hlam, hd23a, hd78b, htr123a, htr128a, htr289a, htr789a]

theorem shard_574 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr014a : m.d 1 4 + lam ≤ m.d 0 1)
    (htr015b : m.d 1 5 < m.d 0 5)
    (htr016b : m.d 1 6 < m.d 0 6)
    (htr017b : m.d 1 7 < m.d 0 7)
    (htr018a : m.d 1 8 + lam ≤ m.d 0 1)
    (htr024a : m.d 0 2 + lam ≤ m.d 2 4)
    (htr025c : m.d 0 5 < m.d 0 2)
    (htr026c : m.d 0 6 < m.d 0 2)
    (htr027c : m.d 0 7 < m.d 0 2)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr125b : m.d 2 5 < m.d 1 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr126b : m.d 2 6 < m.d 1 6)
    (htr127a : m.d 2 7 + lam ≤ m.d 1 2)
    (htr127b : m.d 2 7 < m.d 1 7)
    (htr128a : m.d 1 2 + lam ≤ m.d 2 8)
    (htr128b : m.d 1 2 < m.d 1 8)
    (htr148a : m.d 4 8 + lam ≤ m.d 1 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    : False :=
  proof_shard_574 m htr012b htr014a htr015b htr016b htr017b htr018a htr024a htr025c htr026c htr027c htr035a htr123a htr125a htr125b htr126a htr126b htr127a htr127b htr128a htr128b htr148a htr235a

#print axioms shard_574
end Jsp404.NoSatElevenDBMTerminal
