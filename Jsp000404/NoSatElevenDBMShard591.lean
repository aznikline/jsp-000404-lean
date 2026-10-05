import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_591 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr157a : m.d 5 7 + lam ≤ m.d 1 5)
    (htr158a : m.d 5 8 + lam ≤ m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 4 7)
    (htr248a : m.d 2 4 + lam ≤ m.d 4 8)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr257c : m.d 2 7 < m.d 2 5)
    (htr258c : m.d 2 8 < m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd02a, hd02braw⟩ := m.hrange 0 2 (by decide)
  have hd02b : m.d 0 2 < 4*lam := by
    linarith only [hd02braw, hp]
  have hd23a := (m.hrange 2 3 (by decide)).1
  have hd24a := (m.hrange 2 4 (by decide)).1
  have hd26a := (m.hrange 2 6 (by decide)).1
  have hd27a := (m.hrange 2 7 (by decide)).1
  obtain ⟨hd35a, hd35braw⟩ := m.hrange 3 5 (by decide)
  have hd35b : m.d 3 5 < 4*lam := by
    linarith only [hd35braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd47a, hd47braw⟩ := m.hrange 4 7 (by decide)
  have hd47b : m.d 4 7 < 4*lam := by
    linarith only [hd47braw, hp]
  obtain ⟨hd48a, hd48braw⟩ := m.hrange 4 8 (by decide)
  have hd48b : m.d 4 8 < 4*lam := by
    linarith only [hd48braw, hp]
  obtain ⟨hd67a, hd67braw⟩ := m.hrange 6 7 (by decide)
  have hd67b : m.d 6 7 < 4*lam := by
    linarith only [hd67braw, hp]
  obtain ⟨hd68a, hd68braw⟩ := m.hrange 6 8 (by decide)
  have hd68b : m.d 6 8 < 4*lam := by
    linarith only [hd68braw, hp]
  obtain ⟨hd69a, hd69braw⟩ := m.hrange 6 9 (by decide)
  have hd69b : m.d 6 9 < 4*lam := by
    linarith only [hd69braw, hp]
  obtain ⟨hd610a, hd610braw⟩ := m.hrange 6 10 (by decide)
  have hd610b : m.d 6 10 < 4*lam := by
    linarith only [hd610braw, hp]
  obtain ⟨hd78a, hd78braw⟩ := m.hrange 7 8 (by decide)
  have hd78b : m.d 7 8 < 4*lam := by
    linarith only [hd78braw, hp]
  obtain ⟨hd79a, hd79braw⟩ := m.hrange 7 9 (by decide)
  have hd79b : m.d 7 9 < 4*lam := by
    linarith only [hd79braw, hp]
  obtain ⟨hd710a, hd710braw⟩ := m.hrange 7 10 (by decide)
  have hd710b : m.d 7 10 < 4*lam := by
    linarith only [hd710braw, hp]
  obtain ⟨hd89a, hd89braw⟩ := m.hrange 8 9 (by decide)
  have hd89b : m.d 8 9 < 4*lam := by
    linarith only [hd89braw, hp]
  obtain ⟨hd810a, hd810braw⟩ := m.hrange 8 10 (by decide)
  have hd810b : m.d 8 10 < 4*lam := by
    linarith only [hd810braw, hp]
  obtain ⟨hd910a, hd910braw⟩ := m.hrange 9 10 (by decide)
  have hd910b : m.d 9 10 < 4*lam := by
    linarith only [hd910braw, hp]
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc024xy, hc024yx, hc024yz, hc024zy⟩ := endpoint_caps m 0 2 4 (by decide) (by decide)
  obtain ⟨hc234xy, hc234yx, hc234yz, hc234zy⟩ := endpoint_caps m 2 3 4 (by decide) (by decide)
  obtain ⟨hc236xy, hc236yx, hc236yz, hc236zy⟩ := endpoint_caps m 2 3 6 (by decide) (by decide)
  obtain ⟨hc237xy, hc237yx, hc237yz, hc237zy⟩ := endpoint_caps m 2 3 7 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc247xy, hc247yx, hc247yz, hc247zy⟩ := endpoint_caps m 2 4 7 (by decide) (by decide)
  obtain ⟨hc267xy, hc267yx, hc267yz, hc267zy⟩ := endpoint_caps m 2 6 7 (by decide) (by decide)
  obtain ⟨hc278xy, hc278yx, hc278yz, hc278zy⟩ := endpoint_caps m 2 7 8 (by decide) (by decide)
  obtain ⟨hc279xy, hc279yx, hc279yz, hc279zy⟩ := endpoint_caps m 2 7 9 (by decide) (by decide)
  obtain ⟨hc289xy, hc289yx, hc289yz, hc289zy⟩ := endpoint_caps m 2 8 9 (by decide) (by decide)
  obtain ⟨hc2910xy, hc2910yx, hc2910yz, hc2910zy⟩ := endpoint_caps m 2 9 10 (by decide) (by decide)
  obtain ⟨hc357xy, hc357yx, hc357yz, hc357zy⟩ := endpoint_caps m 3 5 7 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc568xy, hc568yx, hc568yz, hc568zy⟩ := endpoint_caps m 5 6 8 (by decide) (by decide)
  obtain ⟨hc578xy, hc578yx, hc578yz, hc578zy⟩ := endpoint_caps m 5 7 8 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc789xy, hc789yx, hc789yz, hc789zy⟩ := endpoint_caps m 7 8 9 (by decide) (by decide)
  obtain ⟨hc7910xy, hc7910yx, hc7910yz, hc7910zy⟩ := endpoint_caps m 7 9 10 (by decide) (by decide)
  have hforced027 := (m.htr 0 2 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr027a, htr027b, htr027c, _, _⟩
    linarith only [hlam, htr025a, htr027a, htr257c])
  obtain ⟨htr027a, htr027b, htr027c, _, _⟩ := hforced027
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hd02b, hd67a, htr025a, htr125a, htr126a, htr267a])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd02b, hd68a, htr025a, htr125a, htr126a, htr268a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd02b, hd69a, htr025a, htr125a, htr126a, htr269a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hd02b, hd610a, htr025a, htr125a, htr126a, htr2610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  rcases m.htr 1 2 7 (by decide) (by decide) with
    ⟨htr127a, htr127b, htr127c, _, _⟩ | ⟨htr127a, htr127b, htr127c, _, _⟩
  ·
    have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr037a, htr037b, htr037c, _, _⟩
      linarith only [hlam, hc023zy, htr037a, htr123a, htr127a, htr237c])
    obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
    have hforced047 := (m.htr 0 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr047a, htr047b, htr047c, _, _⟩
      linarith only [hlam, hc024zy, htr047a, htr124a, htr127a, htr247c])
    obtain ⟨htr047a, htr047b, htr047c, _, _⟩ := hforced047
    have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr347a, htr347b, htr347c, _, _⟩
      linarith only [hlam, hc234yz, htr124a, htr127a, htr247c, htr347a])
    obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
    have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr367a, htr367b, htr367c, _, _⟩
      linarith only [hlam, hc236yz, htr126a, htr127a, htr267c, htr367a])
    obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
    have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr467a, htr467b, htr467c, _, _⟩
      linarith only [hlam, hc246yz, htr126a, htr127a, htr267c, htr467a])
    obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
    rcases m.htr 3 4 6 (by decide) (by decide) with
      ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
    ·
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hd24a, hd67b, htr248a, htr346a, htr348a, htr467a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      have hforced078 := (m.htr 0 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr078a, htr078b, htr078c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr027b, htr078a, htr123a, htr127a, htr678a])
      obtain ⟨htr078a, htr078b, htr078c, _, _⟩ := hforced078
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr278a, htr678a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr378a, htr378b, htr378c, _, _⟩
        linarith only [hlam, htr037c, htr078a, htr378a])
      obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
      have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr679a, htr679b, htr679c, _, _⟩
        linarith only [hlam, hd23a, hd79b, htr234a, htr346a, htr467a, htr679a])
      obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
      have hforced079 := (m.htr 0 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr079a, htr079b, htr079c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr027b, htr079a, htr123a, htr127a, htr679a])
      obtain ⟨htr079a, htr079b, htr079c, _, _⟩ := hforced079
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hd23a, hd67b, htr123a, htr127a, htr279a, htr679a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr379a, htr379b, htr379c, _, _⟩
        linarith only [hlam, htr037c, htr079a, htr379a])
      obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hc023yx, hc567yz, htr025a, htr034a, htr257c, htr278a, htr346a, htr467a, htr578a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced038 := (m.htr 0 3 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr038a, htr038b, htr038c, _, _⟩
          linarith only [hlam, hc357zy, htr037a, htr038a, htr238c, htr278b, htr578a])
        obtain ⟨htr038a, htr038b, htr038c, _, _⟩ := hforced038
        have hforced389 := (m.htr 3 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr389a, htr389b, htr389c, _, _⟩
          linarith only [hlam, hd23a, hd89b, htr034a, htr038a, htr234a, htr389a])
        obtain ⟨htr389a, htr389b, htr389c, _, _⟩ := hforced389
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd02b, hd79a, htr025a, htr257c, htr278a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced039 := (m.htr 0 3 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr039a, htr039b, htr039c, _, _⟩
          linarith only [hlam, hc357zy, htr037a, htr039a, htr239c, htr279b, htr579a])
        obtain ⟨htr039a, htr039b, htr039c, _, _⟩ := hforced039
        have hforced3910 := (m.htr 3 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr3910a, htr3910b, htr3910c, _, _⟩
          linarith only [hlam, hd23a, hd910b, htr034a, htr039a, htr234a, htr3910a])
        obtain ⟨htr3910a, htr3910b, htr3910c, _, _⟩ := hforced3910
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc357zy, htr378c, htr389a, htr578a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc357zy, htr379c, htr3910a, htr579a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd02b, hd89a, htr025a, htr257c, htr279a, htr7910a, htr8910a]
        ·
          linarith only [hlam, hd02b, hd910a, htr025a, htr257c, htr278a, htr789a, htr8910a]
      ·
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd02b, hd78a, htr025a, htr257c, htr279a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr015a, htr157a, htr578a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd01b, hd910a, htr015a, htr157a, htr579a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 4 6 8 (by decide) (by decide) with
          ⟨htr468a, htr468b, htr468c, _, _⟩ | ⟨htr468a, htr468b, htr468c, _, _⟩
        ·
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hc013yx, hc678zy, htr015a, htr034a, htr157a, htr346a, htr468a, htr578a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr034a, htr036a, htr234a, htr367a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr369a, htr369b, htr369c, _, _⟩
            linarith only [hlam, hd26a, hd35b, htr035a, htr036a, htr269a, htr369a])
          obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
          have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr469a, htr469b, htr469c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr236a, htr369a, htr467a, htr469a])
          obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
          have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr689a, htr689b, htr689c, _, _⟩
            linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr689a])
          obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
          have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
            linarith only [hlam, hd23a, hd910b, htr234a, htr346a, htr469a, htr6910a])
          obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
          rcases m.htr 8 9 10 (by decide) (by decide) with
            ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
          ·
            linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
          ·
            linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
        ·
          have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr368a, htr368b, htr368c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr236a, htr368a, htr467a, htr468a])
          obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
          have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr036a, htr036b, htr036c, _, _⟩
            linarith only [hlam, hd26a, hd35b, htr035a, htr036a, htr268a, htr368a])
          obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
          have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr034a, htr034b, htr034c, _, _⟩
            linarith only [hlam, hd23a, hd67b, htr034a, htr036a, htr234a, htr367a])
          obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
          have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr489a, htr489b, htr489c, _, _⟩
            linarith only [hlam, hc013yx, hc789yz, htr015a, htr034a, htr157a, htr348a, htr489a, htr579a])
          obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
          rcases m.htr 6 8 9 (by decide) (by decide) with
            ⟨htr689a, htr689b, htr689c, _, _⟩ | ⟨htr689a, htr689b, htr689c, _, _⟩
          ·
            linarith only [hlam, hc246yz, htr268a, htr468c, htr489a, htr689a]
          ·
            linarith only [hlam, hd67b, hd78a, htr467a, htr468a, htr689a, htr789a]
    ·
      have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr034a, htr034b, htr034c, _, _⟩
        linarith only [hlam, hd24a, hd35b, htr034a, htr035a, htr246a, htr346a])
      obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
      have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr036a, htr036b, htr036c, _, _⟩
        linarith only [hlam, hd23a, hd45b, htr034a, htr036a, htr236a, htr345a])
      obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc234yz, htr246b, htr268a, htr346a, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hd24a, hd67b, htr246a, htr367a, htr368a, htr468a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr469a, htr469b, htr469c, _, _⟩
        linarith only [hlam, hc234yz, htr246b, htr269a, htr346a, htr469a])
      obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
      have hforced369 := (m.htr 3 6 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr369a, htr369b, htr369c, _, _⟩
        linarith only [hlam, hd24a, hd67b, htr246a, htr367a, htr369a, htr469a])
      obtain ⟨htr369a, htr369b, htr369c, _, _⟩ := hforced369
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hd24a, hd78b, htr246a, htr346a, htr347a, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr278a, htr278b, htr278c, _, _⟩
        linarith only [hlam, hd23a, hd47b, htr123a, htr127a, htr278a, htr478a])
      obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
      have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr479a, htr479b, htr479c, _, _⟩
        linarith only [hlam, hd24a, hd79b, htr246a, htr346a, htr347a, htr479a])
      obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
      have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr279a, htr279b, htr279c, _, _⟩
        linarith only [hlam, hd23a, hd47b, htr123a, htr127a, htr279a, htr479a])
      obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
      have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
        linarith only [hlam, hd24a, hd710b, htr246a, htr346a, htr347a, htr4710a])
      obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
      have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_left (by
        rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
        linarith only [hlam, hd23a, hd47b, htr123a, htr127a, htr2710a, htr4710a])
      obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
      rcases m.htr 5 7 8 (by decide) (by decide) with
        ⟨htr578a, htr578b, htr578c, _, _⟩ | ⟨htr578a, htr578b, htr578c, _, _⟩
      ·
        have hforced046 := (m.htr 0 4 6 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr046a, htr046b, htr046c, _, _⟩
          linarith only [hlam, hc024yx, hc457zy, htr025a, htr046a, htr257c, htr278a, htr346a, htr347a, htr578a])
        obtain ⟨htr046a, htr046b, htr046c, _, _⟩ := hforced046
        have hforced048 := (m.htr 0 4 8 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr048a, htr048b, htr048c, _, _⟩
          linarith only [hlam, hc457zy, htr047a, htr048a, htr478b, htr578a])
        obtain ⟨htr048a, htr048b, htr048c, _, _⟩ := hforced048
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd24a, hd89b, htr046a, htr048a, htr246a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd02b, hd79a, htr025a, htr257c, htr278a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced049 := (m.htr 0 4 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr049a, htr049b, htr049c, _, _⟩
          linarith only [hlam, hc457zy, htr047a, htr049a, htr479b, htr579a])
        obtain ⟨htr049a, htr049b, htr049c, _, _⟩ := hforced049
        have hforced4910 := (m.htr 4 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr4910a, htr4910b, htr4910c, _, _⟩
          linarith only [hlam, hd24a, hd910b, htr046a, htr049a, htr246a, htr4910a])
        obtain ⟨htr4910a, htr4910b, htr4910c, _, _⟩ := hforced4910
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc457zy, htr478c, htr489a, htr578a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hc457zy, htr479c, htr4910a, htr579a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hd02b, hd89a, htr025a, htr257c, htr279a, htr7910a, htr8910a]
        ·
          linarith only [hlam, hd02b, hd910a, htr025a, htr257c, htr278a, htr789a, htr8910a]
      ·
        have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr579a, htr579b, htr579c, _, _⟩
          linarith only [hlam, hd02b, hd78a, htr025a, htr257c, htr279a, htr578a, htr579a])
        obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
        have hforced5710 := (m.htr 5 7 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr5710a, htr5710b, htr5710c, _, _⟩
          linarith only [hlam, hd02b, hd78a, htr025a, htr257c, htr2710a, htr5710a, htr578a])
        obtain ⟨htr5710a, htr5710b, htr5710c, _, _⟩ := hforced5710
        have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr689a, htr689b, htr689c, _, _⟩
          linarith only [hlam, hc013yx, hc789yz, htr015a, htr036a, htr157a, htr368a, htr579a, htr689a])
        obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
        have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
          linarith only [hlam, hc013yx, hc7910yz, htr015a, htr036a, htr157a, htr369a, htr5710a, htr6910a])
        obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hd01b, hd89a, htr015a, htr157a, htr578a, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
          linarith only [hlam, hd01b, hd910a, htr015a, htr157a, htr579a, htr7910a])
        obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
        rcases m.htr 8 9 10 (by decide) (by decide) with
          ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
        ·
          linarith only [hlam, hc678zy, htr689c, htr6910a, htr789a, htr8910a]
        ·
          linarith only [hlam, hc678zy, htr689a, htr789b, htr7910a, htr8910a]
  ·
    have hforced278 := (m.htr 2 7 8 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr278a, htr278b, htr278c, _, _⟩
      linarith only [hlam, hd02b, hd78a, htr025a, htr125a, htr127a, htr278a])
    obtain ⟨htr278a, htr278b, htr278c, _, _⟩ := hforced278
    have hforced279 := (m.htr 2 7 9 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr279a, htr279b, htr279c, _, _⟩
      linarith only [hlam, hd02b, hd79a, htr025a, htr125a, htr127a, htr279a])
    obtain ⟨htr279a, htr279b, htr279c, _, _⟩ := hforced279
    have hforced2710 := (m.htr 2 7 10 (by decide) (by decide)).resolve_right (by
      rintro ⟨htr2710a, htr2710b, htr2710c, _, _⟩
      linarith only [hlam, hd02b, hd710a, htr025a, htr125a, htr127a, htr2710a])
    obtain ⟨htr2710a, htr2710b, htr2710c, _, _⟩ := hforced2710
    rcases m.htr 1 2 8 (by decide) (by decide) with
      ⟨htr128a, htr128b, htr128c, _, _⟩ | ⟨htr128a, htr128b, htr128c, _, _⟩
    ·
      have hforced348 := (m.htr 3 4 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr348a, htr348b, htr348c, _, _⟩
        linarith only [hlam, hc234yz, htr124a, htr128a, htr248c, htr348a])
      obtain ⟨htr348a, htr348b, htr348c, _, _⟩ := hforced348
      have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr368a, htr368b, htr368c, _, _⟩
        linarith only [hlam, hc236yz, htr126a, htr128a, htr268c, htr368a])
      obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
      have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr468a, htr468b, htr468c, _, _⟩
        linarith only [hlam, hc246yz, htr126a, htr128a, htr268c, htr468a])
      obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
      have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr478a, htr478b, htr478c, _, _⟩
        linarith only [hlam, hc247yz, htr127a, htr128a, htr278c, htr478a])
      obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
      have hforced678 := (m.htr 6 7 8 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr678a, htr678b, htr678c, _, _⟩
        linarith only [hlam, hc267yz, htr127a, htr128a, htr278c, htr678a])
      obtain ⟨htr678a, htr678b, htr678c, _, _⟩ := hforced678
      rcases m.htr 3 4 6 (by decide) (by decide) with
        ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
      ·
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hd24a, hd68b, htr247a, htr346a, htr347a, htr468a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hd23a, hd78b, htr234a, htr346a, htr467a, htr678a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hd23a, hd68b, htr236a, htr367a, htr467a, htr468a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd26a, hd35b, htr035a, htr036a, htr267a, htr367a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hd23a, hd68b, htr034a, htr036a, htr234a, htr368a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc246yz, htr267b, htr279a, htr467a, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hd26a, hd78b, htr267a, htr478a, htr479a, htr679a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc013yx, hc789zy, htr015a, htr034a, htr158a, htr347a, htr479a, htr589a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hc023yx, hc568yz, htr025a, htr034a, htr258c, htr289a, htr346a, htr468a, htr589a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        rcases m.htr 7 8 9 (by decide) (by decide) with
          ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
        ·
          linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr678c, htr789a]
        ·
          linarith only [hlam, hd23a, hd78b, htr123a, htr128a, htr289a, htr789a]
      ·
        have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr034a, htr034b, htr034c, _, _⟩
          linarith only [hlam, hd24a, hd35b, htr034a, htr035a, htr246a, htr346a])
        obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
        have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr036a, htr036b, htr036c, _, _⟩
          linarith only [hlam, hd23a, hd45b, htr034a, htr036a, htr236a, htr345a])
        obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
        have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr347a, htr347b, htr347c, _, _⟩
          linarith only [hlam, hd24a, hd78b, htr246a, htr346a, htr347a, htr478a])
        obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
        have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr467a, htr467b, htr467c, _, _⟩
          linarith only [hlam, hc234yz, htr246b, htr267a, htr346a, htr467a])
        obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
        have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr367a, htr367b, htr367c, _, _⟩
          linarith only [hlam, hd24a, hd68b, htr246a, htr367a, htr368a, htr467a])
        obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc234yz, htr247b, htr279a, htr347a, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced489 := (m.htr 4 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr489a, htr489b, htr489c, _, _⟩
          linarith only [hlam, hd24a, hd89b, htr246a, htr346a, htr348a, htr489a])
        obtain ⟨htr489a, htr489b, htr489c, _, _⟩ := hforced489
        have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr289a, htr289b, htr289c, _, _⟩
          linarith only [hlam, hd23a, hd48b, htr123a, htr128a, htr289a, htr489a])
        obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
        have hforced589 := (m.htr 5 8 9 (by decide) (by decide)).resolve_left (by
          rintro ⟨htr589a, htr589b, htr589c, _, _⟩
          linarith only [hlam, hc023yx, hc578yz, htr025a, htr036a, htr258c, htr289a, htr367a, htr589a, htr678a])
        obtain ⟨htr589a, htr589b, htr589c, _, _⟩ := hforced589
        rcases m.htr 6 7 9 (by decide) (by decide) with
          ⟨htr679a, htr679b, htr679c, _, _⟩ | ⟨htr679a, htr679b, htr679c, _, _⟩
        ·
          linarith only [hlam, hc013yx, hc789zy, htr015a, htr036a, htr158a, htr367a, htr589a, htr679a]
        ·
          linarith only [hlam, hd24a, hd78b, htr247a, htr479a, htr678a, htr679a]
    ·
      have hforced289 := (m.htr 2 8 9 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr289a, htr289b, htr289c, _, _⟩
        linarith only [hlam, hd02b, hd89a, htr025a, htr125a, htr128a, htr289a])
      obtain ⟨htr289a, htr289b, htr289c, _, _⟩ := hforced289
      have hforced2810 := (m.htr 2 8 10 (by decide) (by decide)).resolve_right (by
        rintro ⟨htr2810a, htr2810b, htr2810c, _, _⟩
        linarith only [hlam, hd02b, hd810a, htr025a, htr125a, htr128a, htr2810a])
      obtain ⟨htr2810a, htr2810b, htr2810c, _, _⟩ := hforced2810
      rcases m.htr 1 2 9 (by decide) (by decide) with
        ⟨htr129a, htr129b, htr129c, _, _⟩ | ⟨htr129a, htr129b, htr129c, _, _⟩
      ·
        have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr469a, htr469b, htr469c, _, _⟩
          linarith only [hlam, hc246yz, htr126a, htr129a, htr269c, htr469a])
        obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
        have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr479a, htr479b, htr479c, _, _⟩
          linarith only [hlam, hc247yz, htr127a, htr129a, htr279c, htr479a])
        obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
        have hforced679 := (m.htr 6 7 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr679a, htr679b, htr679c, _, _⟩
          linarith only [hlam, hc267yz, htr127a, htr129a, htr279c, htr679a])
        obtain ⟨htr679a, htr679b, htr679c, _, _⟩ := hforced679
        have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr789a, htr789b, htr789c, _, _⟩
          linarith only [hlam, hc278yz, htr128a, htr129a, htr289c, htr789a])
        obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
        rcases m.htr 6 7 8 (by decide) (by decide) with
          ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
        ·
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hd24a, hd89b, htr246a, htr467a, htr678a, htr789a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr346a, htr346b, htr346c, _, _⟩
            linarith only [hlam, hc234yz, htr246b, htr267a, htr346a, htr467a])
          obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
          have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr347a, htr347b, htr347c, _, _⟩
            linarith only [hlam, hd24a, hd69b, htr247a, htr346a, htr347a, htr469a])
          obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hd23a, hd89b, htr234a, htr347a, htr478a, htr789a]
          ·
            linarith only [hlam, hd26a, hd79b, htr267a, htr478a, htr479a, htr678a]
        ·
          have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr467a, htr467b, htr467c, _, _⟩
            linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a])
          obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
          have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr346a, htr346b, htr346c, _, _⟩
            linarith only [hlam, hd23a, hd79b, htr234a, htr346a, htr467a, htr679a])
          obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
          have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
            rintro ⟨htr347a, htr347b, htr347c, _, _⟩
            linarith only [hlam, hd24a, hd79b, htr246a, htr346a, htr347a, htr479a])
          obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
          rcases m.htr 4 7 8 (by decide) (by decide) with
            ⟨htr478a, htr478b, htr478c, _, _⟩ | ⟨htr478a, htr478b, htr478c, _, _⟩
          ·
            linarith only [hlam, hd24a, hd79b, htr247a, htr478a, htr678a, htr679a]
          ·
            linarith only [hlam, hc234yz, htr247b, htr278a, htr347a, htr478a]
      ·
        have hforced2910 := (m.htr 2 9 10 (by decide) (by decide)).resolve_right (by
          rintro ⟨htr2910a, htr2910b, htr2910c, _, _⟩
          linarith only [hlam, hd02b, hd910a, htr025a, htr125a, htr129a, htr2910a])
        obtain ⟨htr2910a, htr2910b, htr2910c, _, _⟩ := hforced2910
        rcases m.htr 1 2 10 (by decide) (by decide) with
          ⟨htr1210a, htr1210b, htr1210c, _, _⟩ | ⟨htr1210a, htr1210b, htr1210c, _, _⟩
        ·
          have hforced3710 := (m.htr 3 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr3710a, htr3710b, htr3710c, _, _⟩
            linarith only [hlam, hc237yz, htr1210a, htr127a, htr2710c, htr3710a])
          obtain ⟨htr3710a, htr3710b, htr3710c, _, _⟩ := hforced3710
          have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
            linarith only [hlam, hc246yz, htr1210a, htr126a, htr2610c, htr4610a])
          obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
          have hforced4710 := (m.htr 4 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr4710a, htr4710b, htr4710c, _, _⟩
            linarith only [hlam, hc247yz, htr1210a, htr127a, htr2710c, htr4710a])
          obtain ⟨htr4710a, htr4710b, htr4710c, _, _⟩ := hforced4710
          have hforced6710 := (m.htr 6 7 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr6710a, htr6710b, htr6710c, _, _⟩
            linarith only [hlam, hc267yz, htr1210a, htr127a, htr2710c, htr6710a])
          obtain ⟨htr6710a, htr6710b, htr6710c, _, _⟩ := hforced6710
          have hforced7810 := (m.htr 7 8 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7810a, htr7810b, htr7810c, _, _⟩
            linarith only [hlam, hc278yz, htr1210a, htr128a, htr2810c, htr7810a])
          obtain ⟨htr7810a, htr7810b, htr7810c, _, _⟩ := hforced7810
          have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
            rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
            linarith only [hlam, hc279yz, htr1210a, htr129a, htr2910c, htr7910a])
          obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd26a, hd710b, htr267a, htr3710a, htr378a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hd27a, hd810b, htr279a, htr378a, htr379a, htr7810a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hd24a, hd810b, htr246a, htr467a, htr678a, htr7810a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr346a, htr346b, htr346c, _, _⟩
              linarith only [hlam, hc234yz, htr246b, htr267a, htr346a, htr467a])
            obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
            have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr347a, htr347b, htr347c, _, _⟩
              linarith only [hlam, hd24a, hd610b, htr247a, htr346a, htr347a, htr4610a])
            obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
            rcases m.htr 4 7 9 (by decide) (by decide) with
              ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd910b, htr234a, htr347a, htr479a, htr7910a]
            ·
              linarith only [hlam, hd23a, hd710b, htr237a, htr379a, htr4710a, htr479a]
          ·
            have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr378a, htr378b, htr378c, _, _⟩
              linarith only [hlam, hd23a, hd710b, htr237a, htr378a, htr6710a, htr678a])
            obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
            have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr379a, htr379b, htr379c, _, _⟩
              linarith only [hlam, hd27a, hd910b, htr278a, htr378a, htr379a, htr7910a])
            obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced346 := (m.htr 3 4 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr346a, htr346b, htr346c, _, _⟩
              linarith only [hlam, hd23a, hd710b, htr234a, htr346a, htr467a, htr6710a])
            obtain ⟨htr346a, htr346b, htr346c, _, _⟩ := hforced346
            have hforced347 := (m.htr 3 4 7 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr347a, htr347b, htr347c, _, _⟩
              linarith only [hlam, hd24a, hd710b, htr246a, htr346a, htr347a, htr4710a])
            obtain ⟨htr347a, htr347b, htr347c, _, _⟩ := hforced347
            rcases m.htr 4 7 9 (by decide) (by decide) with
              ⟨htr479a, htr479b, htr479c, _, _⟩ | ⟨htr479a, htr479b, htr479c, _, _⟩
            ·
              linarith only [hlam, hd24a, hd710b, htr247a, htr3710a, htr379a, htr479a]
            ·
              linarith only [hlam, hc234yz, htr247b, htr279a, htr347a, htr479a]
        ·
          rcases m.htr 6 7 8 (by decide) (by decide) with
            ⟨htr678a, htr678b, htr678c, _, _⟩ | ⟨htr678a, htr678b, htr678c, _, _⟩
          ·
            rcases m.htr 7 8 9 (by decide) (by decide) with
              ⟨htr789a, htr789b, htr789c, _, _⟩ | ⟨htr789a, htr789b, htr789c, _, _⟩
            ·
              have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr367a, htr367b, htr367c, _, _⟩
                linarith only [hlam, hd23a, hd89b, htr236a, htr367a, htr678a, htr789a])
              obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
              have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr036a, htr036b, htr036c, _, _⟩
                linarith only [hlam, hd26a, hd35b, htr035a, htr036a, htr267a, htr367a])
              obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc236yz, htr036a, htr037a, htr267a, htr367b])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              rcases m.htr 3 7 8 (by decide) (by decide) with
                ⟨htr378a, htr378b, htr378c, _, _⟩ | ⟨htr378a, htr378b, htr378c, _, _⟩
              ·
                linarith only [hlam, hc023yx, hc289yz, htr025a, htr037a, htr125a, htr129a, htr378a, htr789a]
              ·
                linarith only [hlam, hc236yz, htr267a, htr367c, htr378a, htr678a]
            ·
              have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr378a, htr378b, htr378c, _, _⟩
                linarith only [hlam, hc237yz, htr278b, htr289a, htr378a, htr789a])
              obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
              have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr379a, htr379b, htr379c, _, _⟩
                linarith only [hlam, hc278yz, htr289a, htr378a, htr379a, htr789b])
              obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
              have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr478a, htr478b, htr478c, _, _⟩
                linarith only [hlam, hc247yz, htr278b, htr289a, htr478a, htr789a])
              obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
              have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr479a, htr479b, htr479c, _, _⟩
                linarith only [hlam, hc278yz, htr289a, htr478a, htr479a, htr789b])
              obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
              have hforced8910 := (m.htr 8 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr8910a, htr8910b, htr8910c, _, _⟩
                linarith only [hlam, hc278yz, htr289b, htr2910a, htr789a, htr8910a])
              obtain ⟨htr8910a, htr8910b, htr8910c, _, _⟩ := hforced8910
              have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_right (by
                rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
                linarith only [hlam, hc278yz, htr289a, htr789c, htr7910a, htr8910a])
              obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
              have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr037a, htr037b, htr037c, _, _⟩
                linarith only [hlam, hc023yx, hc2910yz, htr025a, htr037a, htr1210a, htr125a, htr379a, htr7910a])
              obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
              have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
                rintro ⟨htr034a, htr034b, htr034c, _, _⟩
                linarith only [hlam, hd23a, hd45b, htr034a, htr037a, htr237a, htr345a])
              obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
              rcases m.htr 3 4 7 (by decide) (by decide) with
                ⟨htr347a, htr347b, htr347c, _, _⟩ | ⟨htr347a, htr347b, htr347c, _, _⟩
              ·
                linarith only [hlam, hd23a, hd910b, htr234a, htr347a, htr479a, htr7910a]
              ·
                linarith only [hlam, hd24a, hd35b, htr034a, htr035a, htr247a, htr347a]
          ·
            have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr367a, htr367b, htr367c, _, _⟩
              linarith only [hlam, hc236yz, htr267b, htr278a, htr367a, htr678a])
            obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
            have hforced368 := (m.htr 3 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr368a, htr368b, htr368c, _, _⟩
              linarith only [hlam, hc267yz, htr278a, htr367a, htr368a, htr678b])
            obtain ⟨htr368a, htr368b, htr368c, _, _⟩ := hforced368
            have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr467a, htr467b, htr467c, _, _⟩
              linarith only [hlam, hc246yz, htr267b, htr278a, htr467a, htr678a])
            obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
            have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr468a, htr468b, htr468c, _, _⟩
              linarith only [hlam, hc267yz, htr278a, htr467a, htr468a, htr678b])
            obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
            have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr789a, htr789b, htr789c, _, _⟩
              linarith only [hlam, hc267yz, htr278b, htr289a, htr678a, htr789a])
            obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
            have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
              rintro ⟨htr689a, htr689b, htr689c, _, _⟩
              linarith only [hlam, hc267yz, htr278a, htr678c, htr689a, htr789a])
            obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
            have hforced036 := (m.htr 0 3 6 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr036a, htr036b, htr036c, _, _⟩
              linarith only [hlam, hc023yx, hc289yz, htr025a, htr036a, htr125a, htr129a, htr368a, htr689a])
            obtain ⟨htr036a, htr036b, htr036c, _, _⟩ := hforced036
            have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_left (by
              rintro ⟨htr034a, htr034b, htr034c, _, _⟩
              linarith only [hlam, hd23a, hd45b, htr034a, htr036a, htr236a, htr345a])
            obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
            rcases m.htr 3 4 6 (by decide) (by decide) with
              ⟨htr346a, htr346b, htr346c, _, _⟩ | ⟨htr346a, htr346b, htr346c, _, _⟩
            ·
              linarith only [hlam, hd23a, hd89b, htr234a, htr346a, htr468a, htr689a]
            ·
              linarith only [hlam, hd24a, hd35b, htr034a, htr035a, htr246a, htr346a]

theorem shard_591 {lam p : ℝ} (m : ElevenModel lam p)
    (htr015a : m.d 1 5 + lam ≤ m.d 0 1)
    (htr025a : m.d 2 5 + lam ≤ m.d 0 2)
    (htr035a : m.d 0 3 + lam ≤ m.d 3 5)
    (htr123a : m.d 2 3 + lam ≤ m.d 1 2)
    (htr124a : m.d 2 4 + lam ≤ m.d 1 2)
    (htr125a : m.d 1 2 + lam ≤ m.d 2 5)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr157a : m.d 5 7 + lam ≤ m.d 1 5)
    (htr158a : m.d 5 8 + lam ≤ m.d 1 5)
    (htr234a : m.d 2 3 + lam ≤ m.d 3 4)
    (htr236a : m.d 2 3 + lam ≤ m.d 3 6)
    (htr237a : m.d 2 3 + lam ≤ m.d 3 7)
    (htr237c : m.d 2 7 < m.d 3 7)
    (htr238c : m.d 2 8 < m.d 3 8)
    (htr239c : m.d 2 9 < m.d 3 9)
    (htr246a : m.d 2 4 + lam ≤ m.d 4 6)
    (htr246b : m.d 2 4 < m.d 2 6)
    (htr247a : m.d 2 4 + lam ≤ m.d 4 7)
    (htr247b : m.d 2 4 < m.d 2 7)
    (htr247c : m.d 2 7 < m.d 4 7)
    (htr248a : m.d 2 4 + lam ≤ m.d 4 8)
    (htr248c : m.d 2 8 < m.d 4 8)
    (htr257c : m.d 2 7 < m.d 2 5)
    (htr258c : m.d 2 8 < m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    : False :=
  proof_shard_591 m htr015a htr025a htr035a htr123a htr124a htr125a htr126a htr157a htr158a htr234a htr236a htr237a htr237c htr238c htr239c htr246a htr246b htr247a htr247b htr247c htr248a htr248c htr257c htr258c htr345a

#print axioms shard_591
end Jsp404.NoSatElevenDBMTerminal
