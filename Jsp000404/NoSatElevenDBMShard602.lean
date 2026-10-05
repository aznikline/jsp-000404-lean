import Jsp000404.NoSatElevenDBMModel

namespace Jsp404.NoSatElevenDBMTerminal

set_option maxHeartbeats 32000000 in
private theorem proof_shard_602 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    : False := by
  have hlam := m.hlam
  have hp := m.hp
  obtain ⟨hd01a, hd01braw⟩ := m.hrange 0 1 (by decide)
  have hd01b : m.d 0 1 < 4*lam := by
    linarith only [hd01braw, hp]
  obtain ⟨hd45a, hd45braw⟩ := m.hrange 4 5 (by decide)
  have hd45b : m.d 4 5 < 4*lam := by
    linarith only [hd45braw, hp]
  obtain ⟨hd46a, hd46braw⟩ := m.hrange 4 6 (by decide)
  have hd46b : m.d 4 6 < 4*lam := by
    linarith only [hd46braw, hp]
  have hd57a := (m.hrange 5 7 (by decide)).1
  have hd67a := (m.hrange 6 7 (by decide)).1
  have hd78a := (m.hrange 7 8 (by decide)).1
  have hd79a := (m.hrange 7 9 (by decide)).1
  have hd89a := (m.hrange 8 9 (by decide)).1
  have hd910a := (m.hrange 9 10 (by decide)).1
  obtain ⟨hc013xy, hc013yx, hc013yz, hc013zy⟩ := endpoint_caps m 0 1 3 (by decide) (by decide)
  obtain ⟨hc023xy, hc023yx, hc023yz, hc023zy⟩ := endpoint_caps m 0 2 3 (by decide) (by decide)
  obtain ⟨hc245xy, hc245yx, hc245yz, hc245zy⟩ := endpoint_caps m 2 4 5 (by decide) (by decide)
  obtain ⟨hc246xy, hc246yx, hc246yz, hc246zy⟩ := endpoint_caps m 2 4 6 (by decide) (by decide)
  obtain ⟨hc456xy, hc456yx, hc456yz, hc456zy⟩ := endpoint_caps m 4 5 6 (by decide) (by decide)
  obtain ⟨hc457xy, hc457yx, hc457yz, hc457zy⟩ := endpoint_caps m 4 5 7 (by decide) (by decide)
  obtain ⟨hc567xy, hc567yx, hc567yz, hc567zy⟩ := endpoint_caps m 5 6 7 (by decide) (by decide)
  obtain ⟨hc678xy, hc678yx, hc678yz, hc678zy⟩ := endpoint_caps m 6 7 8 (by decide) (by decide)
  obtain ⟨hc679xy, hc679yx, hc679yz, hc679zy⟩ := endpoint_caps m 6 7 9 (by decide) (by decide)
  obtain ⟨hc6710xy, hc6710yx, hc6710yz, hc6710zy⟩ := endpoint_caps m 6 7 10 (by decide) (by decide)
  obtain ⟨hc689xy, hc689yx, hc689yz, hc689zy⟩ := endpoint_caps m 6 8 9 (by decide) (by decide)
  obtain ⟨hc6910xy, hc6910yx, hc6910yz, hc6910zy⟩ := endpoint_caps m 6 9 10 (by decide) (by decide)
  have hforced357 := (m.htr 3 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr357a, htr357b, htr357c, _, _⟩
    linarith only [hlam, htr345b, htr347c, htr357b])
  obtain ⟨htr357a, htr357b, htr357c, _, _⟩ := hforced357
  have hforced367 := (m.htr 3 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr367a, htr367b, htr367c, _, _⟩
    linarith only [hlam, htr346b, htr347c, htr367b])
  obtain ⟨htr367a, htr367b, htr367c, _, _⟩ := hforced367
  have hforced457 := (m.htr 4 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr457a, htr457b, htr457c, _, _⟩
    linarith only [hlam, htr345c, htr357a, htr457a])
  obtain ⟨htr457a, htr457b, htr457c, _, _⟩ := hforced457
  have hforced257 := (m.htr 2 5 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr257a, htr257b, htr257c, _, _⟩
    linarith only [hlam, hc245yz, htr257a, htr345a, htr347a, htr457b])
  obtain ⟨htr257a, htr257b, htr257c, _, _⟩ := hforced257
  have hforced456 := (m.htr 4 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr456a, htr456b, htr456c, _, _⟩
    linarith only [hlam, hc567yx, htr345a, htr347a, htr456a, htr457b])
  obtain ⟨htr456a, htr456b, htr456c, _, _⟩ := hforced456
  have hforced356 := (m.htr 3 5 6 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr356a, htr356b, htr356c, _, _⟩
    linarith only [hlam, hc457yx, htr345b, htr347a, htr356a, htr456a])
  obtain ⟨htr356a, htr356b, htr356c, _, _⟩ := hforced356
  have hforced467 := (m.htr 4 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr467a, htr467b, htr467c, _, _⟩
    linarith only [hlam, htr346c, htr367a, htr467a])
  obtain ⟨htr467a, htr467b, htr467c, _, _⟩ := hforced467
  have hforced267 := (m.htr 2 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr267a, htr267b, htr267c, _, _⟩
    linarith only [hlam, hc246yz, htr267a, htr346a, htr347a, htr467b])
  obtain ⟨htr267a, htr267b, htr267c, _, _⟩ := hforced267
  have hforced468 := (m.htr 4 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr468a, htr468b, htr468c, _, _⟩
    linarith only [hlam, hc678xy, htr346a, htr347a, htr467b, htr468a])
  obtain ⟨htr468a, htr468b, htr468c, _, _⟩ := hforced468
  have hforced469 := (m.htr 4 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr469a, htr469b, htr469c, _, _⟩
    linarith only [hlam, hc679xy, htr346a, htr347a, htr467b, htr469a])
  obtain ⟨htr469a, htr469b, htr469c, _, _⟩ := hforced469
  have hforced4610 := (m.htr 4 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr4610a, htr4610b, htr4610c, _, _⟩
    linarith only [hlam, hc6710xy, htr346a, htr347a, htr4610a, htr467b])
  obtain ⟨htr4610a, htr4610b, htr4610c, _, _⟩ := hforced4610
  have hforced567 := (m.htr 5 6 7 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr567a, htr567b, htr567c, _, _⟩
    linarith only [hlam, hc456zy, htr346a, htr347a, htr467b, htr567a])
  obtain ⟨htr567a, htr567b, htr567c, _, _⟩ := hforced567
  have hforced256 := (m.htr 2 5 6 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr256a, htr256b, htr256c, _, _⟩
    linarith only [hlam, hd01b, hd67a, htr012a, htr125a, htr256a, htr567a])
  obtain ⟨htr256a, htr256b, htr256c, _, _⟩ := hforced256
  have hforced035 := (m.htr 0 3 5 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr035a, htr035b, htr035c, _, _⟩
    linarith only [hlam, hc023zy, htr035a, htr235b, htr256a, htr356a])
  obtain ⟨htr035a, htr035b, htr035c, _, _⟩ := hforced035
  have hforced034 := (m.htr 0 3 4 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr034a, htr034b, htr034c, _, _⟩
    linarith only [hlam, hc457yx, htr034a, htr035a, htr345c, htr347a])
  obtain ⟨htr034a, htr034b, htr034c, _, _⟩ := hforced034
  have hforced037 := (m.htr 0 3 7 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr037a, htr037b, htr037c, _, _⟩
    linarith only [hlam, hc457yx, htr034a, htr037a, htr345a, htr347b])
  obtain ⟨htr037a, htr037b, htr037c, _, _⟩ := hforced037
  have hforced568 := (m.htr 5 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr568a, htr568b, htr568c, _, _⟩
    linarith only [hlam, hd46b, hd57a, htr256a, htr257a, htr468a, htr568a])
  obtain ⟨htr568a, htr568b, htr568c, _, _⟩ := hforced568
  have hforced268 := (m.htr 2 6 8 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr268a, htr268b, htr268c, _, _⟩
    linarith only [hlam, hd45b, hd67a, htr267a, htr268a, htr456a, htr568a])
  obtain ⟨htr268a, htr268b, htr268c, _, _⟩ := hforced268
  have hforced569 := (m.htr 5 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr569a, htr569b, htr569c, _, _⟩
    linarith only [hlam, hd46b, hd57a, htr256a, htr257a, htr469a, htr569a])
  obtain ⟨htr569a, htr569b, htr569c, _, _⟩ := hforced569
  have hforced269 := (m.htr 2 6 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr269a, htr269b, htr269c, _, _⟩
    linarith only [hlam, hd45b, hd67a, htr267a, htr269a, htr456a, htr569a])
  obtain ⟨htr269a, htr269b, htr269c, _, _⟩ := hforced269
  have hforced5610 := (m.htr 5 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr5610a, htr5610b, htr5610c, _, _⟩
    linarith only [hlam, hd46b, hd57a, htr256a, htr257a, htr4610a, htr5610a])
  obtain ⟨htr5610a, htr5610b, htr5610c, _, _⟩ := hforced5610
  have hforced2610 := (m.htr 2 6 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr2610a, htr2610b, htr2610c, _, _⟩
    linarith only [hlam, hd45b, hd67a, htr2610a, htr267a, htr456a, htr5610a])
  obtain ⟨htr2610a, htr2610b, htr2610c, _, _⟩ := hforced2610
  have hforced578 := (m.htr 5 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr578a, htr578b, htr578c, _, _⟩
    linarith only [hlam, hd01b, hd78a, htr012a, htr125a, htr257a, htr578a])
  obtain ⟨htr578a, htr578b, htr578c, _, _⟩ := hforced578
  have hforced478 := (m.htr 4 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr478a, htr478b, htr478c, _, _⟩
    linarith only [hlam, hd45b, hd57a, htr345a, htr347a, htr478a, htr578a])
  obtain ⟨htr478a, htr478b, htr478c, _, _⟩ := hforced478
  have hforced378 := (m.htr 3 7 8 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr378a, htr378b, htr378c, _, _⟩
    linarith only [hlam, hc457yx, htr345a, htr347c, htr378a, htr478a])
  obtain ⟨htr378a, htr378b, htr378c, _, _⟩ := hforced378
  have hforced579 := (m.htr 5 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr579a, htr579b, htr579c, _, _⟩
    linarith only [hlam, hd01b, hd79a, htr012a, htr125a, htr257a, htr579a])
  obtain ⟨htr579a, htr579b, htr579c, _, _⟩ := hforced579
  have hforced479 := (m.htr 4 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr479a, htr479b, htr479c, _, _⟩
    linarith only [hlam, hd45b, hd57a, htr345a, htr347a, htr479a, htr579a])
  obtain ⟨htr479a, htr479b, htr479c, _, _⟩ := hforced479
  have hforced379 := (m.htr 3 7 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr379a, htr379b, htr379c, _, _⟩
    linarith only [hlam, hc457yx, htr345a, htr347c, htr379a, htr479a])
  obtain ⟨htr379a, htr379b, htr379c, _, _⟩ := hforced379
  have hforced689 := (m.htr 6 8 9 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr689a, htr689b, htr689c, _, _⟩
    linarith only [hlam, hd01b, hd89a, htr012a, htr126a, htr268a, htr689a])
  obtain ⟨htr689a, htr689b, htr689c, _, _⟩ := hforced689
  have hforced6910 := (m.htr 6 9 10 (by decide) (by decide)).resolve_right (by
    rintro ⟨htr6910a, htr6910b, htr6910c, _, _⟩
    linarith only [hlam, hd01b, hd910a, htr012a, htr126a, htr269a, htr6910a])
  obtain ⟨htr6910a, htr6910b, htr6910c, _, _⟩ := hforced6910
  have hforced789 := (m.htr 7 8 9 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr789a, htr789b, htr789c, _, _⟩
    linarith only [hlam, hc013yx, hc689yz, htr012a, htr037a, htr126a, htr269a, htr378a, htr789a])
  obtain ⟨htr789a, htr789b, htr789c, _, _⟩ := hforced789
  have hforced7910 := (m.htr 7 9 10 (by decide) (by decide)).resolve_left (by
    rintro ⟨htr7910a, htr7910b, htr7910c, _, _⟩
    linarith only [hlam, hc013yx, hc6910yz, htr012a, htr037a, htr126a, htr2610a, htr379a, htr7910a])
  obtain ⟨htr7910a, htr7910b, htr7910c, _, _⟩ := hforced7910
  rcases m.htr 8 9 10 (by decide) (by decide) with
    ⟨htr8910a, htr8910b, htr8910c, _, _⟩ | ⟨htr8910a, htr8910b, htr8910c, _, _⟩
  ·
    linarith only [hlam, hc678yz, htr689a, htr789c, htr7910a, htr8910a]
  ·
    linarith only [hlam, hc678yz, htr689b, htr6910a, htr789a, htr8910a]

theorem shard_602 {lam p : ℝ} (m : ElevenModel lam p)
    (htr012a : m.d 1 2 + lam ≤ m.d 0 1)
    (htr125a : m.d 2 5 + lam ≤ m.d 1 2)
    (htr126a : m.d 2 6 + lam ≤ m.d 1 2)
    (htr235b : m.d 2 3 < m.d 2 5)
    (htr345a : m.d 3 4 + lam ≤ m.d 4 5)
    (htr345b : m.d 3 4 < m.d 3 5)
    (htr345c : m.d 3 5 < m.d 4 5)
    (htr346a : m.d 3 4 + lam ≤ m.d 4 6)
    (htr346b : m.d 3 4 < m.d 3 6)
    (htr346c : m.d 3 6 < m.d 4 6)
    (htr347a : m.d 4 7 + lam ≤ m.d 3 4)
    (htr347b : m.d 4 7 < m.d 3 7)
    (htr347c : m.d 3 7 < m.d 3 4)
    : False :=
  proof_shard_602 m htr012a htr125a htr126a htr235b htr345a htr345b htr345c htr346a htr346b htr346c htr347a htr347b htr347c

#print axioms shard_602
end Jsp404.NoSatElevenDBMTerminal
