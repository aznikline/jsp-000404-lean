import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_092 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd12a, hd12braw⟩ := m.hrange 1 2 (by decide)
  have hd12b : m.d 1 2 < 4*lam := by
    linarith only [hd12braw, hp]
  have hd58a := (m.hrange 5 8 (by decide)).1
  have hd68a := (m.hrange 6 8 (by decide)).1
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc348xy, hc348yx, hc348yz, hc348zy⟩ := endpoint_caps m 3 4 8 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc358xy, hc358yx, hc358yz, hc358zy⟩ := endpoint_caps m 3 5 8 (by decide) (by decide)
  obtain ⟨hc458xy, hc458yx, hc458yz, hc458zy⟩ := endpoint_caps m 4 5 8 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr038a, htr038b, htr038c, _, _⟩
    linarith only [hlam, hc012yz, htr023b, htr038a, htr123a, htr238a])
  obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
  have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr048a, htr048b, htr048c, _, _⟩
    linarith only [hlam, htr034b, htr038c, htr048b])
  obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
  have hforced058 := (m.htr 0 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr058a, htr058b, htr058c, _, _⟩
    linarith only [hlam, htr035b, htr038c, htr058b])
  obtain ⟨htr058a, htr058b, htr058c, _, _⟩ := hforced058
  have hforced068 := (m.htr 0 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr068a, htr068b, htr068c, _, _⟩
    linarith only [hlam, htr036b, htr038c, htr068b])
  obtain ⟨htr068a, htr068b, htr068c, _, _⟩ := hforced068
  have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr348a, htr348b, htr348c, _, _⟩
    linarith only [hlam, hc012yz, htr023a, htr024c, htr048a, htr124a, htr234a, htr348a])
  obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc458yx, htr123b, htr134a, htr238a, htr345a, htr348b])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc348yx, htr034b, htr038a, htr045a, htr345a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced358 := (m.htr 3 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr358a, htr358b, htr358c, _, _⟩
    linarith only [hlam, htr025c, htr058a, htr235c, htr358a])
  obtain ⟨htr358a, htr358b, htr358c, _, _⟩ := hforced358
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc568yx, htr123b, htr135a, htr238a, htr356a, htr358b])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc358yx, htr035b, htr038a, htr056a, htr356a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr368a, htr368b, htr368c, _, _⟩
    linarith only [hlam, htr026c, htr068a, htr236c, htr368a])
  obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
  have hforced458 := (m.htr 4 5 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr458a, htr458b, htr458c, _, _⟩
    linarith only [hlam, hc345zy, htr235a, htr238a, htr358b, htr458a])
  obtain ⟨htr458a, htr458b, htr458c, _, _⟩ := hforced458
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd12b, hd58a, htr025c, htr056a, htr125a, htr456a, htr458a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 8 (by decide) (by decide) with
    ⟨htr568a, htr568b, htr568c, _, _⟩ | ⟨htr568a, htr568b, htr568c, _, _⟩
  ·
    linarith only [hlam, hc356zy, htr236a, htr238a, htr368b, htr568a]
  ·
    linarith only [hlam, hd12b, hd68a, htr024c, htr045a, htr124a, htr456a, htr568a]

theorem shard_092 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 0 2 + lam ≤ m.d 2 3)
    (htr023b : m.d 0 2 < m.d 0 3)
    (htr024c : m.d 0 4 < m.d 2 4)
    (htr025c : m.d 0 5 < m.d 2 5)
    (htr026c : m.d 0 6 < m.d 2 6)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr123b : m.d 2 3 < m.d 1 3)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr235a : m.d 2 3 + lam ≤ m.d 3 5)
    (htr235c : m.d 2 5 < m.d 3 5)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr236c : m.d 2 6 < m.d 3 6)
    (htr238a : m.d 3 8 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_092 m htr023a htr023b htr024c htr025c htr026c htr034b htr035b htr036b htr123a htr123b htr124a htr125a htr134a htr135a htr234a htr235a htr235c htr236a htr236c htr238a

#print axioms shard_092
end Jsp404.NoSatElevenDBMTerminal
