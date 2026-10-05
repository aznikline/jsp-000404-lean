import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_009 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd23a, hd23braw⟩ := m.hrange 2 3 (by decide)
  have hd23b : m.d 2 3 < 4*lam := by
    linarith only [hd23braw, hp]
  have hd45a := (m.hrange 4 5 (by decide)).1
  have hd56a := (m.hrange 5 6 (by decide)).1
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc023yz, htr037a, htr134a, htr137a, htr234a])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr047a, htr047b, htr047c, _, _⟩
    linarith only [hlam, htr034b, htr037c, htr047b])
  obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
  have hforced057 := (m.htr 0 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr057a, htr057b, htr057c, _, _⟩
    linarith only [hlam, htr035b, htr037c, htr057b])
  obtain ⟨htr057a, htr057b, htr057c, _, _⟩ := hforced057
  have hforced067 := (m.htr 0 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr067a, htr067b, htr067c, _, _⟩
    linarith only [hlam, htr036b, htr037c, htr067b])
  obtain ⟨htr067a, htr067b, htr067c, _, _⟩ := hforced067
  have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr347a, htr347b, htr347c, _, _⟩
    linarith only [hlam, htr014c, htr047a, htr134c, htr347a])
  obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
  have hforced345 := (m.htr 3 4 5 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr345a, htr345b, htr345c, _, _⟩
    linarith only [hlam, hc457yx, htr013c, htr037a, htr134a, htr345a, htr347b])
  obtain ⟨htr345a, htr345b, htr345c, _, _⟩ := hforced345
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, htr015c, htr057a, htr135c, htr357a])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc567yx, htr013c, htr037a, htr135a, htr356a, htr357b])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, htr016c, htr067a, htr136c, htr367a])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, hd23b, hd45a, htr134a, htr137a, htr234a, htr357b, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hd23b, hd57a, htr235a, htr356a, htr456a, htr457a])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  rcases m.htr 5 6 7 (by decide) (by decide) with
    ⟨htr567a, htr567b, htr567c, _, _⟩ | ⟨htr567a, htr567b, htr567c, _, _⟩
  ·
    linarith only [hlam, hd23b, hd56a, htr134a, htr137a, htr234a, htr367b, htr567a]
  ·
    linarith only [hlam, hd23b, hd67a, htr234a, htr345a, htr456a, htr567a]

theorem shard_009 {lam p : ℝ} (m : ElevenModel lam p)
    (htr013c : m.d 0 3 < m.d 1 3)
    (htr014c : m.d 0 4 < m.d 1 4)
    (htr015c : m.d 0 5 < m.d 1 5)
    (htr016c : m.d 0 6 < m.d 1 6)
    (htr034b : m.d 0 3 < m.d 0 4)
    (htr035b : m.d 0 3 < m.d 0 5)
    (htr036b : m.d 0 3 < m.d 0 6)
    (htr134a : m.d 1 3 + lam ≤ m.d 3 4)
    (htr134c : m.d 1 4 < m.d 3 4)
    (htr135a : m.d 1 3 + lam ≤ m.d 3 5)
    (htr135c : m.d 1 5 < m.d 3 5)
    (htr136c : m.d 1 6 < m.d 3 6)
    (htr137a : m.d 3 7 + lam ≤ m.d 1 3)
    (htr234a : m.d 3 4 + lam ≤ m.d 2 3)
    (htr235a : m.d 3 5 + lam ≤ m.d 2 3)
    : False :=
  proof_shard_009 m htr013c htr014c htr015c htr016c htr034b htr035b htr036b htr134a htr134c htr135a htr135c htr136c htr137a htr234a htr235a

#print axioms shard_009
end Jsp404.NoSatElevenDBMTerminal
