import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_530 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  have hd12a := (m.hrange 1 2 (by decide)).1
  obtain ⟨hd57a, hd57braw⟩ := m.hrange 5 7 (by decide)
  have hd57b : m.d 5 7 < 4*lam := by
    linarith only [hd57braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hc012xy, hc012yx, hc012yz, hc012zy⟩ := endpoint_caps m 0 1 2 (by decide) (by decide)
  obtain ⟨hc345xy, hc345yx, hc345yz, hc345zy⟩ := endpoint_caps m 3 4 5 (by decide) (by decide)
  obtain ⟨hc347xy, hc347yx, hc347yz, hc347zy⟩ := endpoint_caps m 3 4 7 (by decide) (by decide)
  obtain ⟨hc356xy, hc356yx, hc356yz, hc356zy⟩ := endpoint_caps m 3 5 6 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc012zy, htr023c, htr037a, htr123a, htr237a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr034c, htr037b, htr047c])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr035c, htr037b, htr057c])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr036c, htr037b, htr067c])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, hc012zy, htr023a, htr024b, htr047a, htr124a, htr234a, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc457xy, htr123c, htr134a, htr237a, htr345a, htr347c])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced045 := (m.htr 0 4 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr045a, htr045b, htr045c, _, _⟩
    linarith only [hlam, hc347xy, htr034c, htr037a, htr045a, htr345a])
  obtain ⟨htr045a, htr045b, htr045c, _, _⟩ := hforced045
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, htr025b, htr057a, htr235b, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc567xy, htr123c, htr135a, htr237a, htr356a, htr357c])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced056 := (m.htr 0 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr056a, htr056b, htr056c, _, _⟩
    linarith only [hlam, hc357xy, htr035c, htr037a, htr056a, htr356a])
  obtain ⟨htr056a, htr056b, htr056c, _, _⟩ := hforced056
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, htr026b, htr067a, htr236b, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hc345yz, htr235a, htr237a, htr357c, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd12a, hd57b, htr025b, htr056a, htr125a, htr456a, htr457a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    linarith only [hlam, hd12a, hd67b, htr024b, htr045a, htr124a, htr456a, htr567a]
  ·
    linarith only [hlam, hc356yz, htr236a, htr237a, htr367c, htr567a]

theorem shard_530 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023a : m.d 2 3 + lam ≤ m.d 0 2)
    (htr023c : m.d 0 3 < m.d 0 2)
    (htr024b : m.d 2 4 < m.d 0 4)
    (htr025b : m.d 2 5 < m.d 0 5)
    (htr026b : m.d 2 6 < m.d 0 6)
    (htr034c : m.d 0 4 < m.d 0 3)
    (htr035c : m.d 0 5 < m.d 0 3)
    (htr036c : m.d 0 6 < m.d 0 3)
    (htr123a : m.d 1 2 + lam ≤ m.d 2 3)
    (htr123c : m.d 1 3 < m.d 2 3)
    (htr124a : m.d 1 2 + lam ≤ m.d 2 4)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr135a : m.d 3 5 + lam ≤ m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    (htr235b : m.d 3 5 < m.d 2 5)
    (htr236a : m.d 3 6 + lam ≤ m.d 2 3)
    (htr236b : m.d 3 6 < m.d 2 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    : False :=
  proof_shard_530 m htr023a htr023c htr024b htr025b htr026b htr034c htr035c htr036c htr123a htr123c htr124a htr125a htr134a htr135a htr234a htr235a htr235b htr236a htr236b htr237a

#print axioms shard_530
end Jsp404.NoSatElevenDBMTerminal
