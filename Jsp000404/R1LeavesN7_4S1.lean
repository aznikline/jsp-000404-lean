import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h349 | h349
  · rcases m.htr 1 4 5 (by decide) (by decide) with h350 | h350
    · rcases m.htr 2 3 4 (by decide) (by decide) with h351 | h351
      · linarith only [h0, h12, h349, h351, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h353 | h353
        · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
          · rcases m.htr 3 4 5 (by decide) (by decide) with h355 | h355
            · rcases h1bigk with h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c | h356c
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h353, h355, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p356_1]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                rcases p356_3 (m.d 0 1) (by simp) with h359 | h359
                · rcases p356_3 (m.d 1 2) (by simp) with h360 | h360
                  · linarith only [h0, h360, hlam]
                  · linarith only [h360, h9, hlam]
                · linarith only [h359, hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                rcases p356_3 (m.d 0 1) (by simp) with h364 | h364
                · rcases p356_3 (m.d 1 2) (by simp) with h365 | h365
                  · linarith only [h0, h365, hlam]
                  · linarith only [h10, h365, hlam]
                · linarith only [h364, hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                rcases p356_3 (m.d 0 1) (by simp) with h369 | h369
                · rcases p356_3 (m.d 1 2) (by simp) with h370 | h370
                  · linarith only [h0, h370, hlam]
                  · linarith only [h11, h370, hlam]
                · linarith only [h369, hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h0, hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h0, h353, h355, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p356_1]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h0, h12, h353, h355, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p356_1]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                rcases p356_3 (m.d 0 1) (by simp) with h378 | h378
                · rcases p356_3 (m.d 1 2) (by simp) with h379 | h379
                  · rcases p356_3 (m.d 1 3) (by simp) with h380 | h380
                    · linarith only [h380, h9, hlam]
                    · linarith only [h349, h380, hlam]
                  · linarith only [h11, h379, hlam]
                · linarith only [h3, h378, hlam]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h1, hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h9, hlam, p356_1]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h12, hlam, p356_1]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h0, h11, h12, h4, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p356_1]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h2, hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h10, hlam, p356_1]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h2, h353, h355, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p356_1]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                rcases p356_3 (m.d 0 1) (by simp) with h394 | h394
                · rcases p356_3 (m.d 1 2) (by simp) with h395 | h395
                  · rcases p356_3 (m.d 1 3) (by simp) with h396 | h396
                    · linarith only [h12, h396, hlam]
                    · linarith only [h349, h396, hlam]
                  · linarith only [h11, h395, hlam]
                · linarith only [h3, h394, hlam]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h3, hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h11, hlam, p356_1]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h349, hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [h350, hlam, p356_0]
              · have p356_0 := h356c.1
                have p356_1 := h356c.2.1
                have p356_2 := h356c.2.2.1
                have p356_3 := h356c.2.2.2
                linarith only [hlam, p356_0]
            · linarith only [h0, h12, h353, h355, h4, h6, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h12, h349, h350, h351, h353, h354, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h12, h349, h353, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h12, h349, h350, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
    · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
      · linarith only [h12, h411, h9, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
        · linarith only [h349, h413, h9, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
          · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
            · rcases h1bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h10, h415, hc01, hc45, hlam, hphi, ht0b, ht5b, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                rcases p417_3 (m.d 0 1) (by simp) with h420 | h420
                · rcases p417_3 (m.d 1 2) (by simp) with h421 | h421
                  · linarith only [h0, h421, hlam]
                  · linarith only [h421, h9, hlam]
                · linarith only [h420, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                rcases p417_3 (m.d 0 1) (by simp) with h425 | h425
                · rcases p417_3 (m.d 1 2) (by simp) with h426 | h426
                  · linarith only [h0, h426, hlam]
                  · linarith only [h10, h426, hlam]
                · linarith only [h425, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                rcases p417_3 (m.d 0 1) (by simp) with h430 | h430
                · rcases p417_3 (m.d 1 2) (by simp) with h431 | h431
                  · linarith only [h0, h431, hlam]
                  · linarith only [h11, h431, hlam]
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
                rcases p417_3 (m.d 0 1) (by simp) with h437 | h437
                · rcases p417_3 (m.d 1 2) (by simp) with h438 | h438
                  · rcases p417_3 (m.d 1 3) (by simp) with h439 | h439
                    · linarith only [h439, h9, hlam]
                    · rcases p417_3 (m.d 1 4) (by simp) with h441 | h441
                      · linarith only [h10, h441, hlam]
                      · linarith only [h12, h441, hlam]
                  · linarith only [h438, h9, hlam]
                · linarith only [h1, h437, hlam]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h0, h10, h415, hc01, hc45, hlam, hphi, ht0b, ht5b, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                rcases p417_3 (m.d 0 1) (by simp) with h447 | h447
                · rcases p417_3 (m.d 1 2) (by simp) with h448 | h448
                  · rcases p417_3 (m.d 1 3) (by simp) with h449 | h449
                    · linarith only [h449, h9, hlam]
                    · rcases p417_3 (m.d 1 4) (by simp) with h451 | h451
                      · linarith only [h10, h451, hlam]
                      · linarith only [h410, h451, hlam]
                  · linarith only [h11, h448, hlam]
                · linarith only [h3, h447, hlam]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h1, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h9, hlam, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h12, hlam, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h349, hlam, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h2, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h10, hlam, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                rcases p417_3 (m.d 0 1) (by simp) with h463 | h463
                · rcases p417_3 (m.d 1 2) (by simp) with h464 | h464
                  · rcases p417_3 (m.d 1 3) (by simp) with h465 | h465
                    · linarith only [h12, h465, hlam]
                    · rcases p417_3 (m.d 1 4) (by simp) with h467 | h467
                      · rcases p417_3 (m.d 1 5) (by simp) with h468 | h468
                        · linarith only [h410, h468, hlam]
                        · linarith only [h349, h468, hlam]
                      · linarith only [h12, h467, hlam]
                  · linarith only [h464, h9, hlam]
                · linarith only [h1, h463, hlam]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                rcases p417_3 (m.d 0 1) (by simp) with h475 | h475
                · rcases p417_3 (m.d 1 2) (by simp) with h476 | h476
                  · rcases p417_3 (m.d 1 3) (by simp) with h477 | h477
                    · linarith only [h12, h477, hlam]
                    · rcases p417_3 (m.d 1 4) (by simp) with h479 | h479
                      · rcases p417_3 (m.d 1 5) (by simp) with h480 | h480
                        · linarith only [h410, h480, hlam]
                        · rcases h3bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            rcases p482_3 (m.d 0 3) (by simp) with h484 | h484
                            · rcases p482_3 (m.d 1 3) (by simp) with h485 | h485
                              · linarith only [h1, h485, hlam]
                              · rcases p482_3 (m.d 2 3) (by simp) with h487 | h487
                                · linarith only [h4, h487, hlam]
                                · rcases p482_3 (m.d 3 4) (by simp) with h489 | h489
                                  · linarith only [h489, h6, hlam]
                                  · linarith only [h12, h489, hlam]
                            · linarith only [h1, h484, hlam]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            rcases p482_3 (m.d 0 3) (by simp) with h493 | h493
                            · rcases p482_3 (m.d 1 3) (by simp) with h494 | h494
                              · linarith only [h1, h494, hlam]
                              · linarith only [h494, h9, hlam]
                            · linarith only [h4, h493, hlam]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h0, h12, h349, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p417_1, p482_1]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h0, h349, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p482_1]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h1, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h349, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p417_1, p482_1]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h12, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h349, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h4, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h9, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h411, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h413, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h6, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p482_1]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p482_1]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h0, h349, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p482_1]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h7, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h9, hc23, hc35, hlam, hphi, p482_1]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p482_1]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [h416, hlam, p482_0]
                          · have p482_0 := h482c.1
                            have p482_1 := h482c.2.1
                            have p482_2 := h482c.2.2.1
                            have p482_3 := h482c.2.2.2
                            linarith only [hlam, p482_0]
                      · linarith only [h410, h479, hlam]
                  · linarith only [h11, h476, hlam]
                · linarith only [h3, h475, hlam]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h3, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h11, hlam, p417_1]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                rcases p417_3 (m.d 0 1) (by simp) with h525 | h525
                · rcases p417_3 (m.d 1 2) (by simp) with h526 | h526
                  · rcases p417_3 (m.d 1 3) (by simp) with h527 | h527
                    · linarith only [h349, h527, hlam]
                    · rcases p417_3 (m.d 1 4) (by simp) with h529 | h529
                      · rcases p417_3 (m.d 1 5) (by simp) with h530 | h530
                        · rcases h3bigk with h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            rcases p531_3 (m.d 0 3) (by simp) with h533 | h533
                            · rcases p531_3 (m.d 1 3) (by simp) with h534 | h534
                              · linarith only [h1, h534, hlam]
                              · rcases p531_3 (m.d 2 3) (by simp) with h536 | h536
                                · linarith only [h4, h536, hlam]
                                · rcases p531_3 (m.d 3 4) (by simp) with h538 | h538
                                  · linarith only [h538, h6, hlam]
                                  · linarith only [h12, h538, hlam]
                            · linarith only [h1, h533, hlam]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            rcases p531_3 (m.d 0 3) (by simp) with h542 | h542
                            · rcases p531_3 (m.d 1 3) (by simp) with h543 | h543
                              · linarith only [h1, h543, hlam]
                              · linarith only [h543, h9, hlam]
                            · linarith only [h4, h542, hlam]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h0, h10, h12, h4, h415, hc01, hc45, hlam, hphi, ht0b, ht5b, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h0, h349, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h1, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p417_1, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h12, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h349, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h4, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h9, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h411, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h413, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h6, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hc13, hc34, hlam, hphi, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h7, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hc13, hc35, hlam, hphi, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h416, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                        · linarith only [h349, h530, hlam]
                      · linarith only [h12, h529, hlam]
                  · linarith only [h526, h9, hlam]
                · linarith only [h1, h525, hlam]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [h410, hlam, p417_0]
              · have p417_0 := h417c.1
                have p417_1 := h417c.2.1
                have p417_2 := h417c.2.2.1
                have p417_3 := h417c.2.2.2
                linarith only [hlam, p417_0]
            · linarith only [h0, h10, h12, h415, h416, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h576 | h576
            · rcases h1bigk with h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c | h577c
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h10, h410, h411, h415, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                rcases p577_3 (m.d 0 1) (by simp) with h580 | h580
                · rcases p577_3 (m.d 1 2) (by simp) with h581 | h581
                  · linarith only [h0, h581, hlam]
                  · linarith only [h581, h9, hlam]
                · linarith only [h580, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h410, h411, h415, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                rcases p577_3 (m.d 0 1) (by simp) with h586 | h586
                · rcases p577_3 (m.d 1 2) (by simp) with h587 | h587
                  · linarith only [h0, h587, hlam]
                  · linarith only [h11, h587, hlam]
                · linarith only [h586, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h0, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                rcases p577_3 (m.d 0 1) (by simp) with h593 | h593
                · rcases p577_3 (m.d 1 2) (by simp) with h594 | h594
                  · rcases p577_3 (m.d 1 3) (by simp) with h595 | h595
                    · linarith only [h595, h9, hlam]
                    · rcases p577_3 (m.d 1 4) (by simp) with h597 | h597
                      · linarith only [h10, h597, hlam]
                      · linarith only [h12, h597, hlam]
                  · linarith only [h594, h9, hlam]
                · linarith only [h1, h593, hlam]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h0, h410, h411, h415, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h0, h410, h411, h415, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h1, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h9, hlam, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h12, hlam, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h349, hlam, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h2, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h10, hlam, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                rcases p577_3 (m.d 0 1) (by simp) with h611 | h611
                · rcases p577_3 (m.d 1 2) (by simp) with h612 | h612
                  · rcases p577_3 (m.d 1 3) (by simp) with h613 | h613
                    · linarith only [h12, h613, hlam]
                    · rcases p577_3 (m.d 1 4) (by simp) with h615 | h615
                      · rcases p577_3 (m.d 1 5) (by simp) with h616 | h616
                        · linarith only [h410, h616, hlam]
                        · linarith only [h349, h616, hlam]
                      · linarith only [h12, h615, hlam]
                  · linarith only [h612, h9, hlam]
                · linarith only [h1, h611, hlam]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h2, h410, h411, h415, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h3, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h11, hlam, p577_1]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                rcases p577_3 (m.d 0 1) (by simp) with h626 | h626
                · rcases p577_3 (m.d 1 2) (by simp) with h627 | h627
                  · rcases p577_3 (m.d 1 3) (by simp) with h628 | h628
                    · linarith only [h349, h628, hlam]
                    · rcases p577_3 (m.d 1 4) (by simp) with h630 | h630
                      · rcases p577_3 (m.d 1 5) (by simp) with h631 | h631
                        · rcases h3bigk with h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            rcases p632_3 (m.d 0 3) (by simp) with h634 | h634
                            · rcases p632_3 (m.d 1 3) (by simp) with h635 | h635
                              · linarith only [h1, h635, hlam]
                              · rcases p632_3 (m.d 2 3) (by simp) with h637 | h637
                                · linarith only [h4, h637, hlam]
                                · rcases p632_3 (m.d 3 4) (by simp) with h639 | h639
                                  · linarith only [h6, h639, hlam]
                                  · linarith only [h12, h639, hlam]
                            · linarith only [h1, h634, hlam]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            rcases p632_3 (m.d 0 3) (by simp) with h643 | h643
                            · rcases p632_3 (m.d 1 3) (by simp) with h644 | h644
                              · linarith only [h1, h644, hlam]
                              · linarith only [h644, h9, hlam]
                            · linarith only [h4, h643, hlam]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h0, h349, h4, h576, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1, p632_1]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h0, h349, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p577_1, p632_1]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h1, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p577_1, p632_1]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h12, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h349, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h4, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h9, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h411, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h413, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h6, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p632_1]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p632_1]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h0, h349, h4, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p632_1]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h7, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h9, hc23, hc35, hlam, hphi, p632_1]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p632_1]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [h576, hlam, p632_0]
                          · have p632_0 := h632c.1
                            have p632_1 := h632c.2.1
                            have p632_2 := h632c.2.2.1
                            have p632_3 := h632c.2.2.2
                            linarith only [hlam, p632_0]
                        · linarith only [h349, h631, hlam]
                      · linarith only [h12, h630, hlam]
                  · linarith only [h627, h9, hlam]
                · linarith only [h1, h626, hlam]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [h410, hlam, p577_0]
              · have p577_0 := h577c.1
                have p577_1 := h577c.2.1
                have p577_2 := h577c.2.2.1
                have p577_3 := h577c.2.2.2
                linarith only [hlam, p577_0]
            · linarith only [h12, h410, h576, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
      · linarith only [h12, h677, h9, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h679 | h679
        · linarith only [h349, h679, h9, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h681 | h681
          · linarith only [h10, h410, h681, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h683 | h683
            · rcases h1bigk with h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c | h684c
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                rcases p684_3 (m.d 0 1) (by simp) with h686 | h686
                · rcases p684_3 (m.d 1 2) (by simp) with h687 | h687
                  · linarith only [h687, hlam, p684_0]
                  · rcases p684_3 (m.d 1 3) (by simp) with h689 | h689
                    · linarith only [h1, h689, hlam]
                    · rcases p684_3 (m.d 1 4) (by simp) with h691 | h691
                      · linarith only [h2, h691, hlam]
                      · rcases p684_3 (m.d 1 5) (by simp) with h693 | h693
                        · linarith only [h3, h693, hlam]
                        · rcases h3bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            rcases p695_3 (m.d 0 3) (by simp) with h697 | h697
                            · rcases p695_3 (m.d 1 3) (by simp) with h698 | h698
                              · linarith only [h1, h698, hlam]
                              · rcases p695_3 (m.d 2 3) (by simp) with h700 | h700
                                · linarith only [h4, h700, hlam]
                                · rcases p695_3 (m.d 3 4) (by simp) with h702 | h702
                                  · linarith only [h6, h702, hlam]
                                  · linarith only [h12, h702, hlam]
                            · linarith only [h1, h697, hlam]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            rcases p695_3 (m.d 0 3) (by simp) with h706 | h706
                            · rcases p695_3 (m.d 1 3) (by simp) with h707 | h707
                              · linarith only [h1, h707, hlam]
                              · linarith only [h707, h9, hlam]
                            · linarith only [h4, h706, hlam]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h0, h4, h410, h683, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h0, h10, h4, h410, h683, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h1, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h12, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h349, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h4, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h9, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h677, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h679, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h6, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hc13, hc34, hlam, hphi, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h0, h12, h4, h410, h6, h683, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h7, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h9, hc23, hc35, hlam, hphi, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h683, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                · linarith only [h686, hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h0, h12, h4, h410, h6, h683, hlam, p684_2]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h0, h4, h410, h6, h683, hlam, p684_2]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                rcases p684_3 (m.d 0 1) (by simp) with h736 | h736
                · rcases p684_3 (m.d 1 2) (by simp) with h737 | h737
                  · linarith only [h0, h737, hlam]
                  · linarith only [h11, h737, hlam]
                · linarith only [h736, hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h0, hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                rcases p684_3 (m.d 0 1) (by simp) with h743 | h743
                · rcases p684_3 (m.d 1 2) (by simp) with h744 | h744
                  · rcases p684_3 (m.d 1 3) (by simp) with h745 | h745
                    · linarith only [h745, h9, hlam]
                    · rcases p684_3 (m.d 1 4) (by simp) with h747 | h747
                      · linarith only [h10, h747, hlam]
                      · linarith only [h12, h747, hlam]
                  · linarith only [h744, h9, hlam]
                · linarith only [h1, h743, hlam]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                rcases p684_3 (m.d 0 1) (by simp) with h752 | h752
                · rcases p684_3 (m.d 1 2) (by simp) with h753 | h753
                  · rcases p684_3 (m.d 1 3) (by simp) with h754 | h754
                    · linarith only [h754, h9, hlam]
                    · rcases p684_3 (m.d 1 4) (by simp) with h756 | h756
                      · linarith only [h10, h756, hlam]
                      · rcases p684_3 (m.d 1 5) (by simp) with h758 | h758
                        · linarith only [h11, h758, hlam]
                        · linarith only [h410, h758, hlam]
                  · linarith only [h10, h753, hlam]
                · linarith only [h2, h752, hlam]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                rcases p684_3 (m.d 0 1) (by simp) with h763 | h763
                · rcases p684_3 (m.d 1 2) (by simp) with h764 | h764
                  · rcases p684_3 (m.d 1 3) (by simp) with h765 | h765
                    · linarith only [h765, h9, hlam]
                    · rcases p684_3 (m.d 1 4) (by simp) with h767 | h767
                      · linarith only [h10, h767, hlam]
                      · rcases p684_3 (m.d 1 5) (by simp) with h769 | h769
                        · linarith only [h11, h769, hlam]
                        · rcases h3bigk with h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c | h771c
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            rcases p771_3 (m.d 0 3) (by simp) with h773 | h773
                            · rcases p771_3 (m.d 1 3) (by simp) with h774 | h774
                              · linarith only [h1, h774, hlam]
                              · rcases p771_3 (m.d 2 3) (by simp) with h776 | h776
                                · linarith only [h4, h776, hlam]
                                · rcases p771_3 (m.d 3 4) (by simp) with h778 | h778
                                  · linarith only [h6, h778, hlam]
                                  · linarith only [h12, h778, hlam]
                            · linarith only [h1, h773, hlam]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            rcases p771_3 (m.d 0 3) (by simp) with h782 | h782
                            · rcases p771_3 (m.d 1 3) (by simp) with h783 | h783
                              · linarith only [h1, h783, hlam]
                              · linarith only [h783, h9, hlam]
                            · linarith only [h4, h782, hlam]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h0, h4, h683, hc01, hc45, hlam, hphi, ht0b, ht5b, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h0, h349, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h1, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h12, hc23, hc34, hlam, hphi, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h12, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h349, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h4, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h9, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h677, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h679, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h6, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hc13, hc34, hlam, hphi, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h0, h349, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h7, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h9, hc23, hc35, hlam, hphi, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p771_1]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [h683, hlam, p771_0]
                          · have p771_0 := h771c.1
                            have p771_1 := h771c.2.1
                            have p771_2 := h771c.2.2.1
                            have p771_3 := h771c.2.2.2
                            linarith only [hlam, p771_0]
                  · linarith only [h11, h764, hlam]
                · linarith only [h3, h763, hlam]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h1, hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h9, hlam, p684_1]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h12, hlam, p684_1]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h349, hlam, p684_1]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h2, hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h10, hlam, p684_1]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h410, h9, hc23, hc45, hlam, hphi, ht34, p684_1]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h410, hlam, p684_1]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h3, hlam, p684_0]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h11, hlam, p684_1]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h0, h4, h410, h6, h683, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p684_1]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [h0, h4, h410, h6, h683, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p684_1]
              · have p684_0 := h684c.1
                have p684_1 := h684c.2.1
                have p684_2 := h684c.2.2.1
                have p684_3 := h684c.2.2.2
                linarith only [hlam, p684_0]
            · rcases h1bigk with h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                rcases p826_3 (m.d 0 1) (by simp) with h828 | h828
                · rcases p826_3 (m.d 1 2) (by simp) with h829 | h829
                  · linarith only [h829, hlam, p826_0]
                  · rcases p826_3 (m.d 1 3) (by simp) with h831 | h831
                    · linarith only [h1, h831, hlam]
                    · rcases p826_3 (m.d 1 4) (by simp) with h833 | h833
                      · linarith only [h2, h833, hlam]
                      · rcases p826_3 (m.d 1 5) (by simp) with h835 | h835
                        · linarith only [h3, h835, hlam]
                        · rcases h3bigk with h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            rcases p837_3 (m.d 0 3) (by simp) with h839 | h839
                            · rcases p837_3 (m.d 1 3) (by simp) with h840 | h840
                              · linarith only [h1, h840, hlam]
                              · rcases p837_3 (m.d 2 3) (by simp) with h842 | h842
                                · linarith only [h4, h842, hlam]
                                · rcases p837_3 (m.d 3 4) (by simp) with h844 | h844
                                  · linarith only [h6, h844, hlam]
                                  · linarith only [h12, h844, hlam]
                            · linarith only [h1, h839, hlam]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            rcases p837_3 (m.d 0 3) (by simp) with h848 | h848
                            · rcases p837_3 (m.d 1 3) (by simp) with h849 | h849
                              · linarith only [h1, h849, hlam]
                              · linarith only [h849, h9, hlam]
                            · linarith only [h4, h848, hlam]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h0, h12, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h0, h349, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h1, hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h12, hc23, hc34, hlam, hphi, p837_1]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h12, hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h349, hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h4, hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h9, hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h677, hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h679, hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h6, hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [hc13, hc34, hlam, hphi, p837_1]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h683, hlam, p837_1]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h7, hlam, p837_0]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h9, hc23, hc35, hlam, hphi, p837_1]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [h0, h4, h6, h683, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p837_1]
                          · have p837_0 := h837c.1
                            have p837_1 := h837c.2.1
                            have p837_2 := h837c.2.2.1
                            have p837_3 := h837c.2.2.2
                            linarith only [hlam, p837_0]
                · linarith only [h828, hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h0, h12, h4, h6, h683, h8, hlam, p826_2]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                rcases p826_3 (m.d 0 1) (by simp) with h877 | h877
                · rcases p826_3 (m.d 1 2) (by simp) with h878 | h878
                  · linarith only [h0, h878, hlam]
                  · linarith only [h10, h878, hlam]
                · linarith only [h877, hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                rcases p826_3 (m.d 0 1) (by simp) with h882 | h882
                · rcases p826_3 (m.d 1 2) (by simp) with h883 | h883
                  · linarith only [h0, h883, hlam]
                  · linarith only [h11, h883, hlam]
                · linarith only [h882, hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h0, hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                rcases p826_3 (m.d 0 1) (by simp) with h889 | h889
                · rcases p826_3 (m.d 1 2) (by simp) with h890 | h890
                  · rcases p826_3 (m.d 1 3) (by simp) with h891 | h891
                    · linarith only [h891, h9, hlam]
                    · rcases p826_3 (m.d 1 4) (by simp) with h893 | h893
                      · linarith only [h10, h893, hlam]
                      · linarith only [h12, h893, hlam]
                  · linarith only [h890, h9, hlam]
                · linarith only [h1, h889, hlam]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                rcases p826_3 (m.d 0 1) (by simp) with h898 | h898
                · rcases p826_3 (m.d 1 2) (by simp) with h899 | h899
                  · rcases p826_3 (m.d 1 3) (by simp) with h900 | h900
                    · linarith only [h9, h900, hlam]
                    · rcases p826_3 (m.d 1 4) (by simp) with h902 | h902
                      · linarith only [h10, h902, hlam]
                      · rcases p826_3 (m.d 1 5) (by simp) with h904 | h904
                        · linarith only [h11, h904, hlam]
                        · linarith only [h410, h904, hlam]
                  · linarith only [h10, h899, hlam]
                · linarith only [h2, h898, hlam]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                rcases p826_3 (m.d 0 1) (by simp) with h909 | h909
                · rcases p826_3 (m.d 1 2) (by simp) with h910 | h910
                  · rcases p826_3 (m.d 1 3) (by simp) with h911 | h911
                    · linarith only [h9, h911, hlam]
                    · rcases p826_3 (m.d 1 4) (by simp) with h913 | h913
                      · linarith only [h10, h913, hlam]
                      · rcases p826_3 (m.d 1 5) (by simp) with h915 | h915
                        · linarith only [h11, h915, hlam]
                        · rcases h3bigk with h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            rcases p917_3 (m.d 0 3) (by simp) with h919 | h919
                            · rcases p917_3 (m.d 1 3) (by simp) with h920 | h920
                              · linarith only [h1, h920, hlam]
                              · rcases p917_3 (m.d 2 3) (by simp) with h922 | h922
                                · linarith only [h4, h922, hlam]
                                · rcases p917_3 (m.d 3 4) (by simp) with h924 | h924
                                  · linarith only [h6, h924, hlam]
                                  · linarith only [h12, h924, hlam]
                            · linarith only [h1, h919, hlam]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            rcases p917_3 (m.d 0 3) (by simp) with h928 | h928
                            · rcases p917_3 (m.d 1 3) (by simp) with h929 | h929
                              · linarith only [h1, h929, hlam]
                              · linarith only [h9, h929, hlam]
                            · linarith only [h4, h928, hlam]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h0, h12, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h0, h349, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h1, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h12, hc23, hc34, hlam, hphi, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h12, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h349, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h4, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h9, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h677, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h679, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h6, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hc13, hc34, hlam, hphi, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h683, hlam, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h7, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h9, hc23, hc35, hlam, hphi, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h0, h4, h6, h683, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                  · linarith only [h11, h910, hlam]
                · linarith only [h3, h909, hlam]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h1, hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h9, hlam, p826_1]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h12, hlam, p826_1]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h349, hlam, p826_1]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h2, hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h10, hlam, p826_1]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h0, h4, h410, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p826_1]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h410, hlam, p826_1]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h3, hlam, p826_0]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [h11, hlam, p826_1]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                rcases p826_3 (m.d 0 1) (by simp) with h969 | h969
                · rcases p826_3 (m.d 1 2) (by simp) with h970 | h970
                  · rcases p826_3 (m.d 1 3) (by simp) with h971 | h971
                    · linarith only [h349, h971, hlam]
                    · rcases p826_3 (m.d 1 4) (by simp) with h973 | h973
                      · linarith only [h410, h973, hlam]
                      · linarith only [h12, h973, hlam]
                  · linarith only [h9, h970, hlam]
                · linarith only [h1, h969, hlam]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                rcases p826_3 (m.d 0 1) (by simp) with h978 | h978
                · rcases p826_3 (m.d 1 2) (by simp) with h979 | h979
                  · rcases p826_3 (m.d 1 3) (by simp) with h980 | h980
                    · linarith only [h349, h980, hlam]
                    · rcases p826_3 (m.d 1 4) (by simp) with h982 | h982
                      · linarith only [h410, h982, hlam]
                      · rcases p826_3 (m.d 1 5) (by simp) with h984 | h984
                        · rcases h3bigk with h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c | h985c
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            rcases p985_3 (m.d 0 3) (by simp) with h987 | h987
                            · rcases p985_3 (m.d 1 3) (by simp) with h988 | h988
                              · linarith only [h1, h988, hlam]
                              · rcases p985_3 (m.d 2 3) (by simp) with h990 | h990
                                · linarith only [h4, h990, hlam]
                                · rcases p985_3 (m.d 3 4) (by simp) with h992 | h992
                                  · linarith only [h6, h992, hlam]
                                  · linarith only [h12, h992, hlam]
                            · linarith only [h1, h987, hlam]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            rcases p985_3 (m.d 0 3) (by simp) with h996 | h996
                            · rcases p985_3 (m.d 1 3) (by simp) with h997 | h997
                              · linarith only [h1, h997, hlam]
                              · linarith only [h9, h997, hlam]
                            · linarith only [h4, h996, hlam]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h0, h12, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p985_1]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h0, h349, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p985_1]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h1, hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h12, hc23, hc34, hlam, hphi, p985_1]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h12, hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h349, hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h4, hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h9, hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h677, hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h679, hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h6, hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [hc13, hc34, hlam, hphi, p985_1]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p985_1]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h683, hlam, p985_1]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h7, hlam, p985_0]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h9, hc23, hc35, hlam, hphi, p985_1]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p985_1]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [h0, h4, h6, h683, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p985_1]
                          · have p985_0 := h985c.1
                            have p985_1 := h985c.2.1
                            have p985_2 := h985c.2.2.1
                            have p985_3 := h985c.2.2.2
                            linarith only [hlam, p985_0]
                        · linarith only [h410, h984, hlam]
                  · linarith only [h10, h979, hlam]
                · linarith only [h2, h978, hlam]
              · have p826_0 := h826c.1
                have p826_1 := h826c.2.1
                have p826_2 := h826c.2.2.1
                have p826_3 := h826c.2.2.2
                linarith only [hlam, p826_0]

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
  · exact r1l7_11_23_L_I_H_I_s8_x0_x0_x0_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h12
  · exact r1l7_11_23_L_I_H_I_s8_x0_x0_x0_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h12

end R2N4
