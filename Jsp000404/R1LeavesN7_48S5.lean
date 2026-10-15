import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_48S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h355 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
  · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
    · linarith only [h11, h411, h8, hlam]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
      · linarith only [h355, h413, h8, hlam]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
        · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
          · rcases h2bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h0, h415, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p417_1]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              rcases p417_3 (m.d 0 2) (by simp) with h420 | h420
              · rcases p417_3 (m.d 1 2) (by simp) with h421 | h421
                · linarith only [h0, h421, hlam]
                · linarith only [h421, h8, hlam]
              · linarith only [h420, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              rcases p417_3 (m.d 0 2) (by simp) with h425 | h425
              · rcases p417_3 (m.d 1 2) (by simp) with h426 | h426
                · linarith only [h0, h426, hlam]
                · linarith only [h426, h9, hlam]
              · linarith only [h425, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              rcases p417_3 (m.d 0 2) (by simp) with h430 | h430
              · rcases p417_3 (m.d 1 2) (by simp) with h431 | h431
                · linarith only [h0, h431, hlam]
                · linarith only [h10, h431, hlam]
              · linarith only [h430, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h0, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              rcases p417_3 (m.d 0 2) (by simp) with h437 | h437
              · rcases p417_3 (m.d 1 2) (by simp) with h438 | h438
                · rcases p417_3 (m.d 2 3) (by simp) with h439 | h439
                  · linarith only [h439, hlam, p417_0]
                  · rcases p417_3 (m.d 2 4) (by simp) with h441 | h441
                    · linarith only [h441, h9, hlam]
                    · linarith only [h411, h441, hlam]
                · linarith only [h438, hlam, p417_0]
              · linarith only [h2, h437, hlam]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h0, h415, hc01, hc45, hlam, hphi, ht0b, ht5b, p417_1]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              rcases p417_3 (m.d 0 2) (by simp) with h447 | h447
              · rcases p417_3 (m.d 1 2) (by simp) with h448 | h448
                · rcases p417_3 (m.d 2 3) (by simp) with h449 | h449
                  · linarith only [h449, h8, hlam]
                  · rcases p417_3 (m.d 2 4) (by simp) with h451 | h451
                    · linarith only [h451, h9, hlam]
                    · linarith only [h415, h451, hlam]
                · linarith only [h448, hlam, p417_0]
              · linarith only [h4, h447, hlam]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h2, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h8, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h411, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h413, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h3, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h9, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p417_1]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h0, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p417_1]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h4, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h10, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p417_1]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [h415, hlam, p417_0]
            · have p417_0 := h417c.1
              have p417_1 := h417c.2.1
              have p417_2 := h417c.2.2.1
              have p417_3 := h417c.2.2.2
              linarith only [hlam, p417_0]
          · linarith only [h11, h410, h416, hlam]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h472 | h472
          · rcases h2bigk with h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h0, h410, h411, h415, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p473_1]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h11, h2, h410, h411, h415, h5, hlam, p473_2]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h11, h2, h410, h415, h5, hlam, p473_2]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              rcases p473_3 (m.d 0 2) (by simp) with h478 | h478
              · rcases p473_3 (m.d 1 2) (by simp) with h479 | h479
                · linarith only [h0, h479, hlam]
                · linarith only [h10, h479, hlam]
              · linarith only [h478, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h0, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              rcases p473_3 (m.d 0 2) (by simp) with h485 | h485
              · rcases p473_3 (m.d 1 2) (by simp) with h486 | h486
                · rcases p473_3 (m.d 2 3) (by simp) with h487 | h487
                  · linarith only [h487, hlam, p473_0]
                  · rcases p473_3 (m.d 2 4) (by simp) with h489 | h489
                    · linarith only [h489, h9, hlam]
                    · linarith only [h411, h489, hlam]
                · linarith only [h486, hlam, p473_0]
              · linarith only [h2, h485, hlam]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              rcases p473_3 (m.d 0 2) (by simp) with h494 | h494
              · rcases p473_3 (m.d 1 2) (by simp) with h495 | h495
                · rcases p473_3 (m.d 2 3) (by simp) with h496 | h496
                  · linarith only [h496, h8, hlam]
                  · rcases p473_3 (m.d 2 4) (by simp) with h498 | h498
                    · linarith only [h498, hlam, p473_0]
                    · rcases p473_3 (m.d 2 5) (by simp) with h500 | h500
                      · linarith only [h10, h500, hlam]
                      · linarith only [h415, h500, hlam]
                · linarith only [h495, hlam, p473_0]
              · linarith only [h3, h494, hlam]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              rcases p473_3 (m.d 0 2) (by simp) with h505 | h505
              · rcases p473_3 (m.d 1 2) (by simp) with h506 | h506
                · rcases p473_3 (m.d 2 3) (by simp) with h507 | h507
                  · linarith only [h507, h8, hlam]
                  · rcases p473_3 (m.d 2 4) (by simp) with h509 | h509
                    · linarith only [h509, h9, hlam]
                    · rcases p473_3 (m.d 2 5) (by simp) with h511 | h511
                      · linarith only [h511, hlam, p473_0]
                      · rcases h3bigk with h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          rcases p513_3 (m.d 0 3) (by simp) with h515 | h515
                          · rcases p513_3 (m.d 1 3) (by simp) with h516 | h516
                            · linarith only [h1, h516, hlam]
                            · rcases p513_3 (m.d 2 3) (by simp) with h518 | h518
                              · linarith only [h2, h518, hlam]
                              · rcases p513_3 (m.d 3 4) (by simp) with h520 | h520
                                · linarith only [h5, h520, hlam]
                                · linarith only [h11, h520, hlam]
                          · linarith only [h1, h515, hlam]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h11, h410, h411, h415, h5, hlam, p513_2]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h11, h2, h410, h411, h415, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p513_1]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          rcases p513_3 (m.d 0 3) (by simp) with h526 | h526
                          · rcases p513_3 (m.d 1 3) (by simp) with h527 | h527
                            · linarith only [h1, h527, hlam]
                            · rcases p513_3 (m.d 2 3) (by simp) with h529 | h529
                              · linarith only [h2, h529, hlam]
                              · rcases p513_3 (m.d 3 4) (by simp) with h531 | h531
                                · linarith only [h5, h531, hlam]
                                · linarith only [h472, h531, hlam]
                          · linarith only [h526, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h1, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h355, hc23, hc35, hlam, hphi, p513_1]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h11, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h355, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h2, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h8, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h411, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h413, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h5, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          rcases p513_3 (m.d 0 3) (by simp) with h546 | h546
                          · rcases p513_3 (m.d 1 3) (by simp) with h547 | h547
                            · linarith only [h547, hlam, p513_0]
                            · rcases p513_3 (m.d 2 3) (by simp) with h549 | h549
                              · linarith only [h411, h549, hlam]
                              · rcases p513_3 (m.d 3 4) (by simp) with h551 | h551
                                · rcases p513_3 (m.d 3 5) (by simp) with h552 | h552
                                  · linarith only [h472, h552, hlam]
                                  · linarith only [h355, h552, hlam]
                                · linarith only [h551, hlam, p513_0]
                          · linarith only [h1, h546, hlam]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          rcases p513_3 (m.d 0 3) (by simp) with h557 | h557
                          · rcases p513_3 (m.d 1 3) (by simp) with h558 | h558
                            · linarith only [h11, h558, hlam]
                            · linarith only [h558, h8, hlam]
                          · linarith only [h2, h557, hlam]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h0, h2, h355, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p513_1]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h6, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          rcases p513_3 (m.d 0 3) (by simp) with h565 | h565
                          · rcases p513_3 (m.d 1 3) (by simp) with h566 | h566
                            · linarith only [h566, hlam, p513_0]
                            · rcases p513_3 (m.d 2 3) (by simp) with h568 | h568
                              · linarith only [h413, h568, hlam]
                              · rcases p513_3 (m.d 3 4) (by simp) with h570 | h570
                                · rcases p513_3 (m.d 3 5) (by simp) with h571 | h571
                                  · rcases h5bigk with h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      rcases p572_3 (m.d 0 5) (by simp) with h574 | h574
                                      · rcases p572_3 (m.d 1 5) (by simp) with h575 | h575
                                        · linarith only [h575, hlam, p572_0]
                                        · rcases p572_3 (m.d 2 5) (by simp) with h577 | h577
                                          · linarith only [h4, h577, hlam]
                                          · rcases p572_3 (m.d 3 5) (by simp) with h579 | h579
                                            · linarith only [h579, h6, hlam]
                                            · linarith only [h355, h579, hlam]
                                      · linarith only [h574, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      rcases p572_3 (m.d 0 5) (by simp) with h583 | h583
                                      · rcases p572_3 (m.d 1 5) (by simp) with h584 | h584
                                        · linarith only [h0, h10, h584, hc01, hlam, hphi, u0ehi4]
                                        · linarith only [h10, h584, hlam]
                                      · linarith only [h4, h583, hlam]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h8, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p513_1, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      rcases p572_3 (m.d 0 5) (by simp) with h589 | h589
                                      · rcases p572_3 (m.d 1 5) (by simp) with h590 | h590
                                        · linarith only [h0, h2, h355, h590, h6, hc01, hlam, hphi, u0ehi4]
                                        · linarith only [h410, h590, hlam]
                                      · linarith only [h589, h7, hlam]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h0, h11, h2, h410, h5, hc01, hlam, hphi, p572_1, u0ehi4]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      rcases p572_3 (m.d 0 5) (by simp) with h596 | h596
                                      · rcases p572_3 (m.d 1 5) (by simp) with h597 | h597
                                        · rcases p572_3 (m.d 2 5) (by simp) with h598 | h598
                                          · linarith only [h10, h598, hlam]
                                          · rcases p572_3 (m.d 3 5) (by simp) with h600 | h600
                                            · rcases p572_3 (m.d 4 5) (by simp) with h601 | h601
                                              · linarith only [h410, h601, hlam]
                                              · linarith only [h415, h601, hlam]
                                            · linarith only [h413, h600, hlam]
                                        · linarith only [h10, h597, hlam]
                                      · linarith only [h4, h596, hlam]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h355, hlam, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h0, h11, h2, h410, h411, h415, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h4, hlam, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h10, hlam, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h413, hlam, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h415, hlam, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h6, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h0, h2, h410, h411, h415, h472, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      rcases p572_3 (m.d 0 5) (by simp) with h616 | h616
                                      · rcases p572_3 (m.d 1 5) (by simp) with h617 | h617
                                        · linarith only [h355, h617, hlam]
                                        · linarith only [h10, h617, hlam]
                                      · linarith only [h4, h616, hlam]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h0, h2, h411, h415, h472, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h7, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h410, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h0, h11, h2, h410, h411, h415, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h472, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [hlam, p572_0]
                                  · linarith only [h571, hlam, p513_0]
                                · linarith only [h11, h570, hlam]
                          · linarith only [h1, h565, hlam]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          rcases p513_3 (m.d 0 3) (by simp) with h631 | h631
                          · rcases p513_3 (m.d 1 3) (by simp) with h632 | h632
                            · linarith only [h355, h632, hlam]
                            · linarith only [h632, h8, hlam]
                          · linarith only [h2, h631, hlam]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [h472, hlam, p513_0]
                        · have p513_0 := h513c.1
                          have p513_1 := h513c.2.1
                          have p513_2 := h513c.2.2.1
                          have p513_3 := h513c.2.2.2
                          linarith only [hlam, p513_0]
                · linarith only [h506, hlam, p473_0]
              · linarith only [h4, h505, hlam]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h2, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h8, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h411, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h413, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h3, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h9, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p473_1]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h415, hlam, p473_1]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h4, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h10, hlam, p473_0]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p473_1]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p473_1]
            · have p473_0 := h473c.1
              have p473_1 := h473c.2.1
              have p473_2 := h473c.2.2.1
              have p473_3 := h473c.2.2.2
              linarith only [hlam, p473_0]
          · linarith only [h11, h410, h472, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h656 | h656
    · linarith only [h11, h656, h8, hlam]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h658 | h658
      · linarith only [h355, h658, h8, hlam]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h660 | h660
        · linarith only [h0, h410, h660, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h662 | h662
          · rcases h2bigk with h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c | h663c
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              rcases p663_3 (m.d 0 2) (by simp) with h665 | h665
              · rcases p663_3 (m.d 1 2) (by simp) with h666 | h666
                · linarith only [h0, h666, hlam]
                · rcases p663_3 (m.d 2 3) (by simp) with h668 | h668
                  · linarith only [h2, h668, hlam]
                  · rcases p663_3 (m.d 2 4) (by simp) with h670 | h670
                    · linarith only [h3, h670, hlam]
                    · rcases p663_3 (m.d 2 5) (by simp) with h672 | h672
                      · linarith only [h4, h672, hlam]
                      · rcases h3bigk with h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h11, h410, h5, h662, hlam, p674_2]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h11, h410, h5, h662, h8, hlam, p674_2]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h0, h11, h2, h410, h662, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p674_1]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          rcases p674_3 (m.d 0 3) (by simp) with h679 | h679
                          · rcases p674_3 (m.d 1 3) (by simp) with h680 | h680
                            · linarith only [h1, h680, hlam]
                            · rcases p674_3 (m.d 2 3) (by simp) with h682 | h682
                              · linarith only [h2, h682, hlam]
                              · rcases p674_3 (m.d 3 4) (by simp) with h684 | h684
                                · linarith only [h5, h684, hlam]
                                · linarith only [h662, h684, hlam]
                          · linarith only [h679, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h1, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h11, h410, h662, hc23, hc34, hlam, hphi, p674_1]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h11, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h355, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h2, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h8, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h656, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h658, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h5, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          rcases p674_3 (m.d 0 3) (by simp) with h699 | h699
                          · rcases p674_3 (m.d 1 3) (by simp) with h700 | h700
                            · linarith only [h700, hlam, p674_0]
                            · rcases p674_3 (m.d 2 3) (by simp) with h702 | h702
                              · linarith only [h656, h702, hlam]
                              · rcases p674_3 (m.d 3 4) (by simp) with h704 | h704
                                · rcases p674_3 (m.d 3 5) (by simp) with h705 | h705
                                  · linarith only [h662, h705, hlam]
                                  · linarith only [h355, h705, hlam]
                                · linarith only [h704, hlam, p674_0]
                          · linarith only [h1, h699, hlam]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          rcases p674_3 (m.d 0 3) (by simp) with h710 | h710
                          · rcases p674_3 (m.d 1 3) (by simp) with h711 | h711
                            · linarith only [h11, h711, hlam]
                            · linarith only [h711, h8, hlam]
                          · linarith only [h2, h710, hlam]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h0, h11, h2, h410, h5, h662, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p674_1]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h6, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          rcases p674_3 (m.d 0 3) (by simp) with h718 | h718
                          · rcases p674_3 (m.d 1 3) (by simp) with h719 | h719
                            · linarith only [h719, hlam, p674_0]
                            · rcases p674_3 (m.d 2 3) (by simp) with h721 | h721
                              · linarith only [h658, h721, hlam]
                              · rcases p674_3 (m.d 3 4) (by simp) with h723 | h723
                                · rcases p674_3 (m.d 3 5) (by simp) with h724 | h724
                                  · rcases h5bigk with h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [hlam, p725_0]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      rcases p725_3 (m.d 0 5) (by simp) with h727 | h727
                                      · rcases p725_3 (m.d 1 5) (by simp) with h728 | h728
                                        · linarith only [h728, hlam, p725_0]
                                        · rcases p725_3 (m.d 2 5) (by simp) with h730 | h730
                                          · linarith only [h4, h730, hlam]
                                          · rcases p725_3 (m.d 3 5) (by simp) with h732 | h732
                                            · linarith only [h6, h732, hlam]
                                            · linarith only [h355, h732, hlam]
                                      · linarith only [h727, hlam, p725_0]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      rcases p725_3 (m.d 0 5) (by simp) with h736 | h736
                                      · rcases p725_3 (m.d 1 5) (by simp) with h737 | h737
                                        · linarith only [h0, h10, h737, hc01, hlam, hphi, p663_1, u0ehi4]
                                        · linarith only [h10, h737, hlam]
                                      · linarith only [h4, h736, hlam]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h8, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p674_1, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      rcases p725_3 (m.d 0 5) (by simp) with h742 | h742
                                      · rcases p725_3 (m.d 1 5) (by simp) with h743 | h743
                                        · linarith only [h0, h2, h410, h5, h7, h743, hc01, hlam, hphi, u0ehi4]
                                        · rcases p725_3 (m.d 2 5) (by simp) with h745 | h745
                                          · linarith only [h4, h745, hlam]
                                          · rcases p725_3 (m.d 3 5) (by simp) with h747 | h747
                                            · linarith only [h6, h747, hlam]
                                            · linarith only [h662, h747, hlam]
                                      · linarith only [h7, h742, hlam]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h410, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p725_1, u0ehi4]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [hlam, p725_0]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p663_1, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h355, hlam, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h410, hlam, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h4, hlam, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h10, hlam, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [hlam, p725_0]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h658, hlam, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h660, hlam, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h6, hlam, p725_0]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      rcases p725_3 (m.d 0 5) (by simp) with h762 | h762
                                      · rcases p725_3 (m.d 1 5) (by simp) with h763 | h763
                                        · linarith only [h355, h763, hlam]
                                        · rcases p725_3 (m.d 2 5) (by simp) with h765 | h765
                                          · linarith only [h658, h765, hlam]
                                          · rcases p725_3 (m.d 3 5) (by simp) with h767 | h767
                                            · rcases p725_3 (m.d 4 5) (by simp) with h768 | h768
                                              · linarith only [h662, h768, hlam]
                                              · linarith only [h410, h768, hlam]
                                            · linarith only [h355, h767, hlam]
                                      · linarith only [h762, hc35, hlam, hphi, ht01, ht12, ht23, p725_1, u0ehi4]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      rcases p725_3 (m.d 0 5) (by simp) with h773 | h773
                                      · rcases p725_3 (m.d 1 5) (by simp) with h774 | h774
                                        · linarith only [h355, h774, hlam]
                                        · linarith only [h10, h774, hlam]
                                      · linarith only [h4, h773, hlam]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [hlam, p725_0]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h0, h11, h2, h410, h5, h662, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h7, hlam, p725_0]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h0, h10, h2, h5, h656, h660, h662, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h0, h2, h5, h656, h660, h662, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p725_1]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [h662, hlam, p725_0]
                                    · have p725_0 := h725c.1
                                      have p725_1 := h725c.2.1
                                      have p725_2 := h725c.2.2.1
                                      have p725_3 := h725c.2.2.2
                                      linarith only [hlam, p725_0]
                                  · linarith only [h724, hlam, p674_0]
                                · linarith only [h11, h723, hlam]
                          · linarith only [h1, h718, hlam]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          rcases p674_3 (m.d 0 3) (by simp) with h788 | h788
                          · rcases p674_3 (m.d 1 3) (by simp) with h789 | h789
                            · linarith only [h355, h789, hlam]
                            · linarith only [h789, h8, hlam]
                          · linarith only [h2, h788, hlam]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [h662, hlam, p674_0]
                        · have p674_0 := h674c.1
                          have p674_1 := h674c.2.1
                          have p674_2 := h674c.2.2.1
                          have p674_3 := h674c.2.2.2
                          linarith only [hlam, p674_0]
              · linarith only [h0, h665, hlam]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h11, h2, h410, h5, h662, h8, hlam, p663_2]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h2, h410, h5, h662, h9, hlam, p663_2]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              rcases p663_3 (m.d 0 2) (by simp) with h798 | h798
              · rcases p663_3 (m.d 1 2) (by simp) with h799 | h799
                · linarith only [h0, h799, hlam]
                · linarith only [h10, h799, hlam]
              · linarith only [h798, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h0, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              rcases p663_3 (m.d 0 2) (by simp) with h805 | h805
              · rcases p663_3 (m.d 1 2) (by simp) with h806 | h806
                · rcases p663_3 (m.d 2 3) (by simp) with h807 | h807
                  · linarith only [h807, hlam, p663_0]
                  · rcases p663_3 (m.d 2 4) (by simp) with h809 | h809
                    · linarith only [h809, h9, hlam]
                    · linarith only [h656, h809, hlam]
                · linarith only [h806, hlam, p663_0]
              · linarith only [h2, h805, hlam]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              rcases p663_3 (m.d 0 2) (by simp) with h814 | h814
              · rcases p663_3 (m.d 1 2) (by simp) with h815 | h815
                · rcases p663_3 (m.d 2 3) (by simp) with h816 | h816
                  · linarith only [h8, h816, hlam]
                  · rcases p663_3 (m.d 2 4) (by simp) with h818 | h818
                    · linarith only [h818, hlam, p663_0]
                    · rcases p663_3 (m.d 2 5) (by simp) with h820 | h820
                      · linarith only [h10, h820, hlam]
                      · linarith only [h660, h820, hlam]
                · linarith only [h815, hlam, p663_0]
              · linarith only [h3, h814, hlam]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              rcases p663_3 (m.d 0 2) (by simp) with h825 | h825
              · rcases p663_3 (m.d 1 2) (by simp) with h826 | h826
                · rcases p663_3 (m.d 2 3) (by simp) with h827 | h827
                  · linarith only [h8, h827, hlam]
                  · rcases p663_3 (m.d 2 4) (by simp) with h829 | h829
                    · linarith only [h829, h9, hlam]
                    · rcases p663_3 (m.d 2 5) (by simp) with h831 | h831
                      · linarith only [h831, hlam, p663_0]
                      · rcases h3bigk with h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h11, h410, h5, h662, hlam, p833_2]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h11, h410, h5, h662, h8, hlam, p833_2]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h0, h11, h2, h410, h662, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p833_1]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          rcases p833_3 (m.d 0 3) (by simp) with h838 | h838
                          · rcases p833_3 (m.d 1 3) (by simp) with h839 | h839
                            · linarith only [h1, h839, hlam]
                            · rcases p833_3 (m.d 2 3) (by simp) with h841 | h841
                              · linarith only [h2, h841, hlam]
                              · rcases p833_3 (m.d 3 4) (by simp) with h843 | h843
                                · linarith only [h5, h843, hlam]
                                · linarith only [h662, h843, hlam]
                          · linarith only [h838, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h1, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h11, h410, h662, hc23, hc34, hlam, hphi, p833_1]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h11, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h355, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h2, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h8, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h656, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h658, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h5, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          rcases p833_3 (m.d 0 3) (by simp) with h858 | h858
                          · rcases p833_3 (m.d 1 3) (by simp) with h859 | h859
                            · linarith only [h859, hlam, p833_0]
                            · rcases p833_3 (m.d 2 3) (by simp) with h861 | h861
                              · linarith only [h656, h861, hlam]
                              · rcases p833_3 (m.d 3 4) (by simp) with h863 | h863
                                · rcases p833_3 (m.d 3 5) (by simp) with h864 | h864
                                  · linarith only [h662, h864, hlam]
                                  · linarith only [h355, h864, hlam]
                                · linarith only [h863, hlam, p833_0]
                          · linarith only [h1, h858, hlam]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          rcases p833_3 (m.d 0 3) (by simp) with h869 | h869
                          · rcases p833_3 (m.d 1 3) (by simp) with h870 | h870
                            · linarith only [h11, h870, hlam]
                            · linarith only [h8, h870, hlam]
                          · linarith only [h2, h869, hlam]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h0, h11, h2, h410, h5, h662, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p833_1]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h6, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          rcases p833_3 (m.d 0 3) (by simp) with h877 | h877
                          · rcases p833_3 (m.d 1 3) (by simp) with h878 | h878
                            · linarith only [h878, hlam, p833_0]
                            · rcases p833_3 (m.d 2 3) (by simp) with h880 | h880
                              · linarith only [h658, h880, hlam]
                              · rcases p833_3 (m.d 3 4) (by simp) with h882 | h882
                                · rcases p833_3 (m.d 3 5) (by simp) with h883 | h883
                                  · rcases h5bigk with h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c | h884c
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [hlam, p884_0]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      rcases p884_3 (m.d 0 5) (by simp) with h886 | h886
                                      · rcases p884_3 (m.d 1 5) (by simp) with h887 | h887
                                        · linarith only [h887, hlam, p884_0]
                                        · rcases p884_3 (m.d 2 5) (by simp) with h889 | h889
                                          · linarith only [h4, h889, hlam]
                                          · rcases p884_3 (m.d 3 5) (by simp) with h891 | h891
                                            · linarith only [h6, h891, hlam]
                                            · linarith only [h355, h891, hlam]
                                      · linarith only [h886, hlam, p884_0]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      rcases p884_3 (m.d 0 5) (by simp) with h895 | h895
                                      · rcases p884_3 (m.d 1 5) (by simp) with h896 | h896
                                        · linarith only [h0, h10, h896, hc01, hlam, hphi, u0ehi4]
                                        · linarith only [h10, h896, hlam]
                                      · linarith only [h4, h895, hlam]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h8, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p833_1, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      rcases p884_3 (m.d 0 5) (by simp) with h901 | h901
                                      · rcases p884_3 (m.d 1 5) (by simp) with h902 | h902
                                        · linarith only [h0, h2, h410, h5, h7, h902, hc01, hlam, hphi, u0ehi4]
                                        · rcases p884_3 (m.d 2 5) (by simp) with h904 | h904
                                          · linarith only [h4, h904, hlam]
                                          · rcases p884_3 (m.d 3 5) (by simp) with h906 | h906
                                            · linarith only [h6, h906, hlam]
                                            · linarith only [h662, h906, hlam]
                                      · linarith only [h7, h901, hlam]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h410, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p884_1, u0ehi4]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [hlam, p884_0]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h0, h2, h410, h5, h662, hc01, hc25, hlam, hphi, ht0b, ht5b, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h355, hlam, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h410, hlam, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h4, hlam, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h10, hlam, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [hlam, p884_0]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h658, hlam, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h660, hlam, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h6, hlam, p884_0]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      rcases p884_3 (m.d 0 5) (by simp) with h921 | h921
                                      · rcases p884_3 (m.d 1 5) (by simp) with h922 | h922
                                        · linarith only [h355, h922, hlam]
                                        · rcases p884_3 (m.d 2 5) (by simp) with h924 | h924
                                          · linarith only [h658, h924, hlam]
                                          · rcases p884_3 (m.d 3 5) (by simp) with h926 | h926
                                            · rcases p884_3 (m.d 4 5) (by simp) with h927 | h927
                                              · linarith only [h662, h927, hlam]
                                              · linarith only [h410, h927, hlam]
                                            · linarith only [h355, h926, hlam]
                                      · linarith only [h0, h2, h5, h662, h921, hc01, hlam, hphi, p884_1, u0ehi4]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      rcases p884_3 (m.d 0 5) (by simp) with h932 | h932
                                      · rcases p884_3 (m.d 1 5) (by simp) with h933 | h933
                                        · linarith only [h355, h933, hlam]
                                        · linarith only [h10, h933, hlam]
                                      · linarith only [h4, h932, hlam]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [hlam, p884_0]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h0, h11, h2, h410, h5, h662, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h7, hlam, p884_0]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h0, h10, h2, h5, h656, h660, h662, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h0, h2, h5, h656, h660, h662, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p884_1]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [h662, hlam, p884_0]
                                    · have p884_0 := h884c.1
                                      have p884_1 := h884c.2.1
                                      have p884_2 := h884c.2.2.1
                                      have p884_3 := h884c.2.2.2
                                      linarith only [hlam, p884_0]
                                  · linarith only [h883, hlam, p833_0]
                                · linarith only [h11, h882, hlam]
                          · linarith only [h1, h877, hlam]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          rcases p833_3 (m.d 0 3) (by simp) with h947 | h947
                          · rcases p833_3 (m.d 1 3) (by simp) with h948 | h948
                            · linarith only [h355, h948, hlam]
                            · linarith only [h8, h948, hlam]
                          · linarith only [h2, h947, hlam]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [h662, hlam, p833_0]
                        · have p833_0 := h833c.1
                          have p833_1 := h833c.2.1
                          have p833_2 := h833c.2.2.1
                          have p833_3 := h833c.2.2.2
                          linarith only [hlam, p833_0]
                · linarith only [h826, hlam, p663_0]
              · linarith only [h4, h825, hlam]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h2, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h8, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h656, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h658, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h3, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h9, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p663_1]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h660, hlam, p663_1]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h4, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h10, hlam, p663_0]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h0, h10, h2, h410, h5, h662, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p663_1]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [h0, h10, h2, h410, h5, h662, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p663_1]
            · have p663_0 := h663c.1
              have p663_1 := h663c.2.1
              have p663_2 := h663c.2.2.1
              have p663_3 := h663c.2.2.2
              linarith only [hlam, p663_0]
          · rcases h2bigk with h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              rcases p971_3 (m.d 0 2) (by simp) with h973 | h973
              · rcases p971_3 (m.d 1 2) (by simp) with h974 | h974
                · linarith only [h0, h974, hlam]
                · rcases p971_3 (m.d 2 3) (by simp) with h976 | h976
                  · linarith only [h2, h976, hlam]
                  · rcases p971_3 (m.d 2 4) (by simp) with h978 | h978
                    · linarith only [h3, h978, hlam]
                    · rcases p971_3 (m.d 2 5) (by simp) with h980 | h980
                      · linarith only [h4, h980, hlam]
                      · rcases h3bigk with h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h11, h5, h662, h7, hlam, p982_2]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h11, h5, h662, h7, h8, hlam, p982_2]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          rcases p982_3 (m.d 0 3) (by simp) with h986 | h986
                          · rcases p982_3 (m.d 1 3) (by simp) with h987 | h987
                            · linarith only [h1, h987, hlam]
                            · rcases p982_3 (m.d 2 3) (by simp) with h989 | h989
                              · linarith only [h2, h989, hlam]
                              · rcases p982_3 (m.d 3 4) (by simp) with h991 | h991
                                · linarith only [h991, hlam, p982_0]
                                · rcases p982_3 (m.d 3 5) (by simp) with h993 | h993
                                  · linarith only [h6, h993, hlam]
                                  · linarith only [h662, h993, hlam]
                          · linarith only [h986, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          rcases p982_3 (m.d 0 3) (by simp) with h997 | h997
                          · rcases p982_3 (m.d 1 3) (by simp) with h998 | h998
                            · linarith only [h1, h998, hlam]
                            · rcases p982_3 (m.d 2 3) (by simp) with h1000 | h1000
                              · linarith only [h1000, h2, hlam]
                              · rcases p982_3 (m.d 3 4) (by simp) with h1002 | h1002
                                · linarith only [h1002, h5, hlam]
                                · rcases p982_3 (m.d 3 5) (by simp) with h1004 | h1004
                                  · linarith only [h1004, hlam, p982_0]
                                  · rcases h5bigk with h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      rcases p1006_3 (m.d 0 5) (by simp) with h1008 | h1008
                                      · rcases p1006_3 (m.d 1 5) (by simp) with h1009 | h1009
                                        · linarith only [h1009, hlam, p1006_0]
                                        · rcases p1006_3 (m.d 2 5) (by simp) with h1011 | h1011
                                          · linarith only [h1011, h4, hlam]
                                          · rcases p1006_3 (m.d 3 5) (by simp) with h1013 | h1013
                                            · linarith only [h1013, h6, hlam]
                                            · linarith only [h1013, h355, hlam]
                                      · linarith only [h1008, hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      rcases p1006_3 (m.d 0 5) (by simp) with h1017 | h1017
                                      · rcases p1006_3 (m.d 1 5) (by simp) with h1018 | h1018
                                        · linarith only [h0, h10, h1018, hc01, hlam, hphi, u0ehi4]
                                        · linarith only [h10, h1018, hlam]
                                      · linarith only [h1017, h4, hlam]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      rcases p1006_3 (m.d 0 5) (by simp) with h1022 | h1022
                                      · rcases p1006_3 (m.d 1 5) (by simp) with h1023 | h1023
                                        · linarith only [h1023, h355, hlam, p1006_1]
                                        · rcases p1006_3 (m.d 2 5) (by simp) with h1025 | h1025
                                          · linarith only [h1025, h4, hlam]
                                          · rcases p1006_3 (m.d 3 5) (by simp) with h1027 | h1027
                                            · linarith only [h1027, h6, hlam]
                                            · rcases p1006_3 (m.d 4 5) (by simp) with h1029 | h1029
                                              · linarith only [h1029, h7, hlam]
                                              · linarith only [h1029, h662, hlam]
                                      · linarith only [h1022, h6, hlam]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h0, h11, h2, h5, h662, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h355, hc35, hlam, hphi, ht01, ht12, ht23, p1006_1, u0ehi4]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h0, h2, h355, h656, h660, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1006_1, p982_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h355, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h410, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h4, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h10, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h658, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h660, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h6, hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h0, h2, hc01, hc15, hlam, hphi, ht0b, ht5b, p1006_1, p982_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h0, h2, h656, h660, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1006_1, p982_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h662, hlam, p1006_1]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h7, hlam, p1006_0]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      rcases p1006_3 (m.d 0 5) (by simp) with h1050 | h1050
                                      · rcases p1006_3 (m.d 1 5) (by simp) with h1051 | h1051
                                        · linarith only [h1051, h410, hlam]
                                        · rcases p1006_3 (m.d 2 5) (by simp) with h1053 | h1053
                                          · linarith only [h1053, h660, hlam]
                                          · rcases p1006_3 (m.d 3 5) (by simp) with h1055 | h1055
                                            · linarith only [h1055, h662, hlam]
                                            · linarith only [h1055, h355, hlam]
                                      · linarith only [h1050, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1006_1, u0ehi4]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      rcases p1006_3 (m.d 0 5) (by simp) with h1059 | h1059
                                      · rcases p1006_3 (m.d 1 5) (by simp) with h1060 | h1060
                                        · linarith only [h1060, h410, hlam]
                                        · linarith only [h10, h1060, hlam]
                                      · linarith only [h1059, h4, hlam]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [h5, h7, hlam, p1006_1, p982_2]
                                    · have p1006_0 := h1006c.1
                                      have p1006_1 := h1006c.2.1
                                      have p1006_2 := h1006c.2.2.1
                                      have p1006_3 := h1006c.2.2.2
                                      linarith only [hlam, p1006_0]
                          · linarith only [h997, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h1, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h0, h11, h2, h5, h662, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h11, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h355, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h2, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h8, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h656, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h658, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h5, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h0, h2, h5, h662, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h0, h2, h5, h662, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h662, hlam, p982_1]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h6, hlam, p982_0]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          rcases p982_3 (m.d 0 3) (by simp) with h1083 | h1083
                          · rcases p982_3 (m.d 1 3) (by simp) with h1084 | h1084
                            · linarith only [h1084, hlam, p982_0]
                            · rcases p982_3 (m.d 2 3) (by simp) with h1086 | h1086
                              · linarith only [h1086, h658, hlam]
                              · rcases p982_3 (m.d 3 4) (by simp) with h1088 | h1088
                                · linarith only [h1088, h662, hlam]
                                · linarith only [h1088, h11, hlam]
                          · linarith only [h1, h1083, hlam]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          rcases p982_3 (m.d 0 3) (by simp) with h1092 | h1092
                          · rcases p982_3 (m.d 1 3) (by simp) with h1093 | h1093
                            · linarith only [h1093, h355, hlam]
                            · linarith only [h1093, h8, hlam]
                          · linarith only [h1092, h2, hlam]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [h0, h11, h2, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1]
                        · have p982_0 := h982c.1
                          have p982_1 := h982c.2.1
                          have p982_2 := h982c.2.2.1
                          have p982_3 := h982c.2.2.2
                          linarith only [hlam, p982_0]
              · linarith only [h0, h973, hlam]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h11, h2, h5, h662, h7, h8, hlam, p971_2]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              rcases p971_3 (m.d 0 2) (by simp) with h1101 | h1101
              · rcases p971_3 (m.d 1 2) (by simp) with h1102 | h1102
                · linarith only [h0, h1102, hlam]
                · linarith only [h1102, h9, hlam]
              · linarith only [h1101, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              rcases p971_3 (m.d 0 2) (by simp) with h1106 | h1106
              · rcases p971_3 (m.d 1 2) (by simp) with h1107 | h1107
                · linarith only [h0, h1107, hlam]
                · linarith only [h10, h1107, hlam]
              · linarith only [h1106, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h0, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              rcases p971_3 (m.d 0 2) (by simp) with h1113 | h1113
              · rcases p971_3 (m.d 1 2) (by simp) with h1114 | h1114
                · rcases p971_3 (m.d 2 3) (by simp) with h1115 | h1115
                  · linarith only [h1115, hlam, p971_0]
                  · rcases p971_3 (m.d 2 4) (by simp) with h1117 | h1117
                    · linarith only [h1117, h9, hlam]
                    · linarith only [h1117, h656, hlam]
                · linarith only [h1114, hlam, p971_0]
              · linarith only [h1113, h2, hlam]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              rcases p971_3 (m.d 0 2) (by simp) with h1122 | h1122
              · rcases p971_3 (m.d 1 2) (by simp) with h1123 | h1123
                · rcases p971_3 (m.d 2 3) (by simp) with h1124 | h1124
                  · linarith only [h1124, h8, hlam]
                  · rcases p971_3 (m.d 2 4) (by simp) with h1126 | h1126
                    · linarith only [h1126, hlam, p971_0]
                    · rcases p971_3 (m.d 2 5) (by simp) with h1128 | h1128
                      · linarith only [h10, h1128, hlam]
                      · linarith only [h1128, h660, hlam]
                · linarith only [h1123, hlam, p971_0]
              · linarith only [h1122, h3, hlam]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              rcases p971_3 (m.d 0 2) (by simp) with h1133 | h1133
              · rcases p971_3 (m.d 1 2) (by simp) with h1134 | h1134
                · rcases p971_3 (m.d 2 3) (by simp) with h1135 | h1135
                  · linarith only [h1135, h8, hlam]
                  · rcases p971_3 (m.d 2 4) (by simp) with h1137 | h1137
                    · linarith only [h1137, h9, hlam]
                    · rcases p971_3 (m.d 2 5) (by simp) with h1139 | h1139
                      · linarith only [h1139, hlam, p971_0]
                      · rcases h3bigk with h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c | h1141c
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h11, h5, h662, h7, hlam, p1141_2]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h11, h5, h662, h7, h8, hlam, p1141_2]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          rcases p1141_3 (m.d 0 3) (by simp) with h1145 | h1145
                          · rcases p1141_3 (m.d 1 3) (by simp) with h1146 | h1146
                            · linarith only [h1, h1146, hlam]
                            · rcases p1141_3 (m.d 2 3) (by simp) with h1148 | h1148
                              · linarith only [h1148, h2, hlam]
                              · rcases p1141_3 (m.d 3 4) (by simp) with h1150 | h1150
                                · linarith only [h1150, hlam, p1141_0]
                                · rcases p1141_3 (m.d 3 5) (by simp) with h1152 | h1152
                                  · linarith only [h1152, h6, hlam]
                                  · linarith only [h1152, h662, hlam]
                          · linarith only [h1145, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          rcases p1141_3 (m.d 0 3) (by simp) with h1156 | h1156
                          · rcases p1141_3 (m.d 1 3) (by simp) with h1157 | h1157
                            · linarith only [h1, h1157, hlam]
                            · rcases p1141_3 (m.d 2 3) (by simp) with h1159 | h1159
                              · linarith only [h1159, h2, hlam]
                              · rcases p1141_3 (m.d 3 4) (by simp) with h1161 | h1161
                                · linarith only [h1161, h5, hlam]
                                · rcases p1141_3 (m.d 3 5) (by simp) with h1163 | h1163
                                  · linarith only [h1163, hlam, p1141_0]
                                  · rcases h5bigk with h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [hlam, p1165_0]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      rcases p1165_3 (m.d 0 5) (by simp) with h1167 | h1167
                                      · rcases p1165_3 (m.d 1 5) (by simp) with h1168 | h1168
                                        · linarith only [h1168, hlam, p1165_0]
                                        · rcases p1165_3 (m.d 2 5) (by simp) with h1170 | h1170
                                          · linarith only [h1170, h4, hlam]
                                          · rcases p1165_3 (m.d 3 5) (by simp) with h1172 | h1172
                                            · linarith only [h1172, h6, hlam]
                                            · linarith only [h1172, h355, hlam]
                                      · linarith only [h1167, hlam, p1165_0]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      rcases p1165_3 (m.d 0 5) (by simp) with h1176 | h1176
                                      · rcases p1165_3 (m.d 1 5) (by simp) with h1177 | h1177
                                        · linarith only [h0, h10, h1177, hc01, hlam, hphi, u0ehi4]
                                        · linarith only [h10, h1177, hlam]
                                      · linarith only [h1176, h4, hlam]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      rcases p1165_3 (m.d 0 5) (by simp) with h1181 | h1181
                                      · rcases p1165_3 (m.d 1 5) (by simp) with h1182 | h1182
                                        · linarith only [h1182, h355, hlam, p1165_1]
                                        · rcases p1165_3 (m.d 2 5) (by simp) with h1184 | h1184
                                          · linarith only [h1184, h4, hlam]
                                          · rcases p1165_3 (m.d 3 5) (by simp) with h1186 | h1186
                                            · linarith only [h1186, h6, hlam]
                                            · rcases p1165_3 (m.d 4 5) (by simp) with h1188 | h1188
                                              · linarith only [h1188, h7, hlam]
                                              · linarith only [h1188, h662, hlam]
                                      · linarith only [h1181, h6, hlam]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h0, h11, h2, h5, h662, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h355, hc35, hlam, hphi, ht01, ht12, ht23, p1165_1, u0ehi4]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [hlam, p1165_0]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h0, h2, h355, h660, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1141_1, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h355, hlam, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h410, hlam, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h4, hlam, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h10, hlam, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [hlam, p1165_0]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h658, hlam, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h660, hlam, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h6, hlam, p1165_0]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h0, h2, hc01, hc15, hlam, hphi, ht0b, ht5b, p1141_1, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h0, h2, h656, h660, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1141_1, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [hlam, p1165_0]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h662, hlam, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h7, hlam, p1165_0]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      rcases p1165_3 (m.d 0 5) (by simp) with h1209 | h1209
                                      · rcases p1165_3 (m.d 1 5) (by simp) with h1210 | h1210
                                        · linarith only [h1210, h410, hlam]
                                        · rcases p1165_3 (m.d 2 5) (by simp) with h1212 | h1212
                                          · linarith only [h1212, h660, hlam]
                                          · rcases p1165_3 (m.d 3 5) (by simp) with h1214 | h1214
                                            · linarith only [h1214, h662, hlam]
                                            · linarith only [h1214, h355, hlam]
                                      · linarith only [h1209, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1165_1, u0ehi4]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      rcases p1165_3 (m.d 0 5) (by simp) with h1218 | h1218
                                      · rcases p1165_3 (m.d 1 5) (by simp) with h1219 | h1219
                                        · linarith only [h1219, h410, hlam]
                                        · linarith only [h10, h1219, hlam]
                                      · linarith only [h1218, h4, hlam]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [h5, h7, hlam, p1141_2, p1165_1]
                                    · have p1165_0 := h1165c.1
                                      have p1165_1 := h1165c.2.1
                                      have p1165_2 := h1165c.2.2.1
                                      have p1165_3 := h1165c.2.2.2
                                      linarith only [hlam, p1165_0]
                          · linarith only [h1156, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h1, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h0, h11, h2, h5, h662, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1141_1]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h11, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h355, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h2, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h8, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h656, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h658, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h5, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h0, h2, h5, h662, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1141_1]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h0, h2, h5, h662, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1141_1]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h662, hlam, p1141_1]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h6, hlam, p1141_0]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          rcases p1141_3 (m.d 0 3) (by simp) with h1242 | h1242
                          · rcases p1141_3 (m.d 1 3) (by simp) with h1243 | h1243
                            · linarith only [h1243, hlam, p1141_0]
                            · rcases p1141_3 (m.d 2 3) (by simp) with h1245 | h1245
                              · linarith only [h1245, h658, hlam]
                              · rcases p1141_3 (m.d 3 4) (by simp) with h1247 | h1247
                                · linarith only [h1247, h662, hlam]
                                · linarith only [h11, h1247, hlam]
                          · linarith only [h1, h1242, hlam]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          rcases p1141_3 (m.d 0 3) (by simp) with h1251 | h1251
                          · rcases p1141_3 (m.d 1 3) (by simp) with h1252 | h1252
                            · linarith only [h1252, h355, hlam]
                            · linarith only [h1252, h8, hlam]
                          · linarith only [h1251, h2, hlam]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [h0, h11, h2, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1141_1]
                        · have p1141_0 := h1141c.1
                          have p1141_1 := h1141c.2.1
                          have p1141_2 := h1141c.2.2.1
                          have p1141_3 := h1141c.2.2.2
                          linarith only [hlam, p1141_0]
                · linarith only [h1134, hlam, p971_0]
              · linarith only [h1133, h4, hlam]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h2, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h8, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h656, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h658, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h3, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h9, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h660, hlam, p971_1]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h4, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h10, hlam, p971_0]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p971_1]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p971_1]
            · have p971_0 := h971c.1
              have p971_1 := h971c.2.1
              have p971_2 := h971c.2.2.1
              have p971_3 := h971c.2.2.2
              linarith only [hlam, p971_0]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 5 (by decide) (by decide) with h355 | h355
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10 h11 h355
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10 h11 h355

end R2N4
