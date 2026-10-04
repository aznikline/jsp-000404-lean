import Jsp000404.NoSatNineDBMModel

namespace Jsp404.NoSatNineDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_156 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr578a : m.d 5 7 + lam ≤ m.d 7 8)
    (htr578b : m.d 5 7 < m.d 5 8)
    (htr578c : m.d 5 8 < m.d 7 8)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256b : m.d 5 6 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr357a : m.d 5 7 + lam ≤ m.d 3 5)
    (htr357b : m.d 5 7 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr478a : m.d 4 7 + lam ≤ m.d 7 8)
    (htr478b : m.d 4 7 < m.d 4 8)
    (htr478c : m.d 4 8 < m.d 7 8)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd03a, hd03braw⟩ := m.hrange 0 3 (by decide)
  have hd03b : m.d 0 3 < (7/2 : ℝ)*lam := by
    linarith only [hd03braw, hp]
  have hd12a := (m.hrange 1 2 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  obtain ⟨hd34a, hd34braw⟩ := m.hrange 3 4 (by decide)
  have hd34b : m.d 3 4 < (7/2 : ℝ)*lam := by
    linarith only [hd34braw, hp]
  have hd56a := (m.hrange 5 6 (by decide)).1
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < (7/2 : ℝ)*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc034xy, hc034yx, hc034yz, hc034zy⟩ := endpoint_caps m 0 3 4 (by decide) (by decide)
  obtain ⟨hc035xy, hc035yx, hc035yz, hc035zy⟩ := endpoint_caps m 0 3 5 (by decide) (by decide)
  obtain ⟨hc056xy, hc056yx, hc056yz, hc056zy⟩ := endpoint_caps m 0 5 6 (by decide) (by decide)
  obtain ⟨hc124xy, hc124yx, hc124yz, hc124zy⟩ := endpoint_caps m 1 2 4 (by decide) (by decide)
  obtain ⟨hc125xy, hc125yx, hc125yz, hc125zy⟩ := endpoint_caps m 1 2 5 (by decide) (by decide)
  obtain ⟨hc134xy, hc134yx, hc134yz, hc134zy⟩ := endpoint_caps m 1 3 4 (by decide) (by decide)
  obtain ⟨hc156xy, hc156yx, hc156yz, hc156zy⟩ := endpoint_caps m 1 5 6 (by decide) (by decide)
  obtain ⟨hc256xy, hc256yx, hc256yz, hc256zy⟩ := endpoint_caps m 2 5 6 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hd03b, hd56a, htr034a, htr345c, htr357a, htr456a, htr457a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, hd34b, hd56a, htr034a, htr035a, htr357a, htr456a, htr457a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hd34b, hd56a, htr034a, htr037a, htr357b, htr456a, htr457a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc034yz, htr045a, htr345c, htr357a, htr457a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr046a, htr046b, htr046c, _, _⟩
    linarith only [hlam, htr045a, htr046a, htr456c])
  obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, hd34b, hd56a, htr045a, htr047a, htr347a, htr456a])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, htr045b, htr056a, htr456a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, hc056zy, htr067a, htr456a, htr457a, htr567c])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr067a, htr068a, htr678b])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr078a, htr078b, htr078c, _, _⟩
    linarith only [hlam, htr067c, htr078a, htr678a])
  obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, htr037b, htr038c, htr078b])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced128 := (m.htr 1 2 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr128a, htr128b, htr128c, _, _⟩
    linarith only [hlam, hc278yz, hd34b, hd56a, htr123a, htr128a, htr234a, htr456a, htr457a, htr567c, htr678a])
  obtain ⟨htr128a, htr128b, htr128c, _, _⟩ := hforced128
  have hforced137 := (m.htr 1 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr137a, htr137b, htr137c, _, _⟩
    linarith only [hlam, htr013b, htr037a, htr137a])
  obtain ⟨htr137a, htr137b, htr137c, _, _⟩ := hforced137
  have hforced127 := (m.htr 1 2 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr127a, htr127b, htr127c, _, _⟩
    linarith only [hlam, htr123b, htr127c, htr137b])
  obtain ⟨htr127a, htr127b, htr127c, _, _⟩ := hforced127
  have hforced138 := (m.htr 1 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr138a, htr138b, htr138c, _, _⟩
    linarith only [hlam, htr013b, htr038a, htr138a])
  obtain ⟨htr138a, htr138b, htr138c, _, _⟩ := hforced138
  have hforced145 := (m.htr 1 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr145a, htr145b, htr145c, _, _⟩
    linarith only [hlam, hc134yz, htr145a, htr345c, htr357a, htr457a])
  obtain ⟨htr145a, htr145b, htr145c, _, _⟩ := hforced145
  have hforced146 := (m.htr 1 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr146a, htr146b, htr146c, _, _⟩
    linarith only [hlam, htr145a, htr146a, htr456c])
  obtain ⟨htr146a, htr146b, htr146c, _, _⟩ := hforced146
  have hforced147 := (m.htr 1 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr147a, htr147b, htr147c, _, _⟩
    linarith only [hlam, hd34b, hd56a, htr145a, htr147a, htr347a, htr456a])
  obtain ⟨htr147a, htr147b, htr147c, _, _⟩ := hforced147
  have hforced156 := (m.htr 1 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr156a, htr156b, htr156c, _, _⟩
    linarith only [hlam, htr145b, htr156a, htr456a])
  obtain ⟨htr156a, htr156b, htr156c, _, _⟩ := hforced156
  have hforced167 := (m.htr 1 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr167a, htr167b, htr167c, _, _⟩
    linarith only [hlam, hc156zy, htr167a, htr456a, htr457a, htr567c])
  obtain ⟨htr167a, htr167b, htr167c, _, _⟩ := hforced167
  have hforced016 := (m.htr 0 1 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr016a, htr016b, htr016c, _, _⟩
    linarith only [hlam, hd12a, hd78b, htr012a, htr016a, htr167a, htr678a])
  obtain ⟨htr016a, htr016b, htr016c, _, _⟩ := hforced016
  have hforced168 := (m.htr 1 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr168a, htr168b, htr168c, _, _⟩
    linarith only [hlam, htr167a, htr168a, htr678b])
  obtain ⟨htr168a, htr168b, htr168c, _, _⟩ := hforced168
  have hforced178 := (m.htr 1 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr178a, htr178b, htr178c, _, _⟩
    linarith only [hlam, htr167c, htr178a, htr678a])
  obtain ⟨htr178a, htr178b, htr178c, _, _⟩ := hforced178
  have hforced237 := (m.htr 2 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr237a, htr237b, htr237c, _, _⟩
    linarith only [hlam, hd34b, hd56a, htr234a, htr237a, htr357b, htr456a, htr457a])
  obtain ⟨htr237a, htr237b, htr237c, _, _⟩ := hforced237
  have hforced245 := (m.htr 2 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr245a, htr245b, htr245c, _, _⟩
    linarith only [hlam, htr124c, htr145a, htr245a])
  obtain ⟨htr245a, htr245b, htr245c, _, _⟩ := hforced245
  have hforced246 := (m.htr 2 4 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr246a, htr246b, htr246c, _, _⟩
    linarith only [hlam, htr124c, htr145a, htr246a, htr456c])
  obtain ⟨htr246a, htr246b, htr246c, _, _⟩ := hforced246
  have hforced247 := (m.htr 2 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr247a, htr247b, htr247c, _, _⟩
    linarith only [hlam, htr124c, htr147a, htr247a])
  obtain ⟨htr247a, htr247b, htr247c, _, _⟩ := hforced247
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc256zy, htr267a, htr456a, htr457a, htr567c])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, htr267a, htr268a, htr678b])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr278a, htr278b, htr278c, _, _⟩
    linarith only [hlam, htr267c, htr278a, htr678a])
  obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
  have hforced238 := (m.htr 2 3 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr238a, htr238b, htr238c, _, _⟩
    linarith only [hlam, htr237b, htr238c, htr278b])
  obtain ⟨htr238a, htr238b, htr238c, _, _⟩ := hforced238
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc458xy, htr345c, htr348a, htr357a, htr457a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, hd34b, hd56a, htr045a, htr048a, htr348a, htr456a])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced148 := (m.htr 1 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr148a, htr148b, htr148c, _, _⟩
    linarith only [hlam, hd34b, hd56a, htr145a, htr148a, htr348a, htr456a])
  obtain ⟨htr148a, htr148b, htr148c, _, _⟩ := hforced148
  have hforced248 := (m.htr 2 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr248a, htr248b, htr248c, _, _⟩
    linarith only [hlam, htr124c, htr148a, htr248a])
  obtain ⟨htr248a, htr248b, htr248c, _, _⟩ := hforced248
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, hc568xy, htr357a, htr358a, htr456a, htr457a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, hc356zy, htr367a, htr456a, htr457a, htr567c])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced024 := (m.htr 0 2 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr024a, htr024b, htr024c, _, _⟩
    linarith only [hlam, hc012zy, hd56a, hd78b, htr024a, htr123a, htr124c, htr145a, htr237a, htr367c, htr456a, htr678a])
  obtain ⟨htr024a, htr024b, htr024c, _, _⟩ := hforced024
  have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr036a, htr036b, htr036c, _, _⟩
    linarith only [hlam, hc356yx, hd56a, hd78b, htr036a, htr037a, htr357a, htr367c, htr456a, htr457a, htr678a])
  obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
  have hforced014 := (m.htr 0 1 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr014a, htr014b, htr014c, _, _⟩
    linarith only [hlam, hc013yx, hd56a, hd78b, htr014a, htr036a, htr145a, htr367a, htr456a, htr678a])
  obtain ⟨htr014a, htr014b, htr014c, _, _⟩ := hforced014
  have hforced015 := (m.htr 0 1 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr015a, htr015b, htr015c, _, _⟩
    linarith only [hlam, hc124xy, hd56a, hd78b, htr014a, htr015a, htr123a, htr145b, htr237a, htr367c, htr456a, htr678a])
  obtain ⟨htr015a, htr015b, htr015c, _, _⟩ := hforced015
  have hforced017 := (m.htr 0 1 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr017a, htr017b, htr017c, _, _⟩
    linarith only [hlam, hc124xy, hd56a, hd78b, htr014a, htr017a, htr123a, htr147b, htr237a, htr367c, htr456a, htr457b, htr678a])
  obtain ⟨htr017a, htr017b, htr017c, _, _⟩ := hforced017
  have hforced018 := (m.htr 0 1 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr018a, htr018b, htr018c, _, _⟩
    linarith only [hlam, htr017a, htr018a, htr178b])
  obtain ⟨htr018a, htr018b, htr018c, _, _⟩ := hforced018
  have hforced023 := (m.htr 0 2 3 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr023a, htr023b, htr023c, _, _⟩
    linarith only [hlam, hc124xy, htr012c, htr014a, htr023a, htr123a])
  obtain ⟨htr023a, htr023b, htr023c, _, _⟩ := hforced023
  have hforced026 := (m.htr 0 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr026a, htr026b, htr026c, _, _⟩
    linarith only [hlam, hd26a, hd78b, htr023a, htr026a, htr237a, htr367c, htr678a])
  obtain ⟨htr026a, htr026b, htr026c, _, _⟩ := hforced026
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, hc035xy, hd56a, hd78b, htr036a, htr057a, htr367a, htr456a, htr457a, htr678a])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr057a, htr058a, htr578b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced126 := (m.htr 1 2 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr126a, htr126b, htr126c, _, _⟩
    linarith only [hlam, htr012b, htr026a, htr126a])
  obtain ⟨htr126a, htr126b, htr126c, _, _⟩ := hforced126
  have hforced136 := (m.htr 1 3 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr136a, htr136b, htr136c, _, _⟩
    linarith only [hlam, htr013b, htr036a, htr136a])
  obtain ⟨htr136a, htr136b, htr136c, _, _⟩ := hforced136
  rcases m.htr 1 5 7 (by decide) (by decide) with
    ⟨htr157a, htr157b, htr157c, _, _⟩ | ⟨htr157a, htr157b, htr157c, _, _⟩
  ·
    linarith only [hlam, hd12a, hd78b, htr012a, htr015a, htr157a, htr567c, htr678a]
  ·
    linarith only [hlam, hc125xy, htr012a, htr015b, htr057a, htr157a]

theorem shard_156 {lam p : ℝ} (m : NineModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr012b : m.d 1 2 < m.d 0 2)
    (htr012c : m.d 0 2 < m.d 0 1)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123b : m.d 1 2 < m.d 1 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr234b : m.d 2 3 < m.d 2 4)
    (htr234c : m.d 2 4 < m.d 3 4)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr124b : m.d 1 2 < m.d 1 4)
    (htr124c : m.d 1 4 < m.d 2 4)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134b : m.d 1 3 < m.d 1 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345b : m.d 4 5 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 3 4)
    (htr456a : m.d 5 6 + lam ≤ m.d 4 5)
    (htr456b : m.d 5 6 < m.d 4 6)
    (htr456c : m.d 4 6 < m.d 4 5)
    (htr346a : m.d 4 6 + lam ≤ m.d 3 4)
    (htr346b : m.d 4 6 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 3 4)
    (htr356a : m.d 5 6 + lam ≤ m.d 3 5)
    (htr356b : m.d 5 6 < m.d 3 6)
    (htr356c : m.d 3 6 < m.d 3 5)
    (htr567a : m.d 5 6 + lam ≤ m.d 6 7)
    (htr567b : m.d 5 6 < m.d 5 7)
    (htr567c : m.d 5 7 < m.d 6 7)
    (htr678a : m.d 6 7 + lam ≤ m.d 7 8)
    (htr678b : m.d 6 7 < m.d 6 8)
    (htr678c : m.d 6 8 < m.d 7 8)
    (htr568a : m.d 5 6 + lam ≤ m.d 6 8)
    (htr568b : m.d 5 6 < m.d 5 8)
    (htr568c : m.d 5 8 < m.d 6 8)
    (htr578a : m.d 5 7 + lam ≤ m.d 7 8)
    (htr578b : m.d 5 7 < m.d 5 8)
    (htr578c : m.d 5 8 < m.d 7 8)
    (htr013a : m.d 1 3 + lam ≤ m.d 0 1)
    (htr013b : m.d 1 3 < m.d 0 3)
    (htr013c : m.d 0 3 < m.d 0 1)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr125b : m.d 1 2 < m.d 1 5)
    (htr125c : m.d 1 5 < m.d 2 5)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135b : m.d 1 3 < m.d 1 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr256a : m.d 5 6 + lam ≤ m.d 2 5)
    (htr256b : m.d 5 6 < m.d 2 6)
    (htr256c : m.d 2 6 < m.d 2 5)
    (htr357a : m.d 5 7 + lam ≤ m.d 3 5)
    (htr357b : m.d 5 7 < m.d 3 7)
    (htr357c : m.d 3 7 < m.d 3 5)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    (htr478a : m.d 4 7 + lam ≤ m.d 7 8)
    (htr478b : m.d 4 7 < m.d 4 8)
    (htr478c : m.d 4 8 < m.d 7 8)
    (htr457a : m.d 4 5 + lam ≤ m.d 5 7)
    (htr457b : m.d 4 5 < m.d 4 7)
    (htr457c : m.d 4 7 < m.d 5 7)
    : False :=
  proof_shard_156 m htr012a htr012b htr012c htr123a htr123b htr123c htr234a htr234b htr234c htr124a htr124b htr124c htr134a htr134b htr134c htr345a htr345b htr345c htr456a htr456b htr456c htr346a htr346b htr346c htr356a htr356b htr356c htr567a htr567b htr567c htr678a htr678b htr678c htr568a htr568b htr568c htr578a htr578b htr578c htr013a htr013b htr013c htr235a htr235b htr235c htr125a htr125b htr125c htr135a htr135b htr135c htr256a htr256b htr256c htr357a htr357b htr357c htr347a htr347b htr347c htr478a htr478b htr478c htr457a htr457b htr457c

#print axioms shard_156
end Jsp404.NoSatNineDBMTerminal
