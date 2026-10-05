import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_181 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd13a, hd13braw⟩ := m.hrange 1 3 (by decide)
  have hd13b : m.d 1 3 < 4*lam := by
    linarith only [hd13braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, htr023b, htr037a, htr237a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr035b, htr037c, htr057b])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr036b, htr037c, htr067b])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, htr035c, htr057a, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc567yx, htr023b, htr035a, htr237a, htr356a, htr357b])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, htr036c, htr067a, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd13b, hd45a, htr134a, htr234a, htr237a, htr357b, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd13b, hd57a, htr134a, htr345c, htr356a, htr456a, htr457a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    linarith only [hlam, hd13b, hd56a, htr134a, htr234a, htr237a, htr367b, htr567a]
  ·
    linarith only [hlam, hd13b, hd67a, htr134a, htr345a, htr456a, htr567a]

theorem shard_181 {lam p : ℝ} (m : ElevenModel lam p)
    (htr023b : m.d 2 3 < m.d 0 3)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr035c : m.d 0 5 < m.d 3 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr036c : m.d 0 6 < m.d 3 6)
    (htr134a : m.d 3 4 + lam ≤ m.d 1 3)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr237a : m.d 3 7 + lam ≤ m.d 2 3)
    (htr345a : m.d 4 5 + lam ≤ m.d 3 4)
    (htr345c : m.d 3 5 < m.d 3 4)
    : False :=
  proof_shard_181 m htr023b htr035a htr035b htr035c htr036b htr036c htr134a htr234a htr237a htr345a htr345c

#print axioms shard_181
end Jsp404.NoSatElevenDBMTerminal
