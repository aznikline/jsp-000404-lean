import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_53S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
  · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
    · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
      · linarith only [h11, h363, h8, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h365 | h365
        · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
          · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
            · rcases h2bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h0, h365, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p368_1]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                rcases p368_3 (m.d 0 2) (by simp) with h371 | h371
                · rcases p368_3 (m.d 1 2) (by simp) with h372 | h372
                  · linarith only [h0, h372, hlam]
                  · linarith only [h372, h8, hlam]
                · linarith only [h371, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                rcases p368_3 (m.d 0 2) (by simp) with h376 | h376
                · rcases p368_3 (m.d 1 2) (by simp) with h377 | h377
                  · linarith only [h0, h377, hlam]
                  · linarith only [h377, h9, hlam]
                · linarith only [h376, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                rcases p368_3 (m.d 0 2) (by simp) with h381 | h381
                · rcases p368_3 (m.d 1 2) (by simp) with h382 | h382
                  · linarith only [h0, h382, hlam]
                  · linarith only [h10, h382, hlam]
                · linarith only [h381, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h0, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h0, h365, h367, hc01, hc45, hlam, hphi, ht0b, ht5b, p368_1]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h0, h363, h365, h367, hc01, hc45, hlam, hphi, ht0b, ht5b, p368_1]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                rcases p368_3 (m.d 0 2) (by simp) with h390 | h390
                · rcases p368_3 (m.d 1 2) (by simp) with h391 | h391
                  · rcases p368_3 (m.d 2 3) (by simp) with h392 | h392
                    · linarith only [h392, h8, hlam]
                    · linarith only [h365, h392, hlam]
                  · linarith only [h391, hlam, p368_0]
                · linarith only [h390, h5, hlam]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h3, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h8, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h363, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h0, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p368_1]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h4, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h9, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p368_1]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h0, h365, h367, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p368_1]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h5, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h10, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h365, hlam, p368_1]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [h366, hlam, p368_0]
              · have p368_0 := h368c.1
                have p368_1 := h368c.2.1
                have p368_2 := h368c.2.2.1
                have p368_3 := h368c.2.2.2
                linarith only [hlam, p368_0]
            · linarith only [h0, h11, h3, h365, h367, h6, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h11, h3, h361, h362, h363, h365, h366, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h11, h3, h361, h365, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h11, h361, h362, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h416 | h416
    · rcases m.htr 2 3 4 (by decide) (by decide) with h417 | h417
      · linarith only [h11, h417, h8, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h419 | h419
        · linarith only [h361, h419, h8, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
          · rcases m.htr 3 4 5 (by decide) (by decide) with h422 | h422
            · rcases h2bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h0, h421, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p423_1]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                rcases p423_3 (m.d 0 2) (by simp) with h426 | h426
                · rcases p423_3 (m.d 1 2) (by simp) with h427 | h427
                  · linarith only [h0, h427, hlam]
                  · linarith only [h427, h8, hlam]
                · linarith only [h426, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                rcases p423_3 (m.d 0 2) (by simp) with h431 | h431
                · rcases p423_3 (m.d 1 2) (by simp) with h432 | h432
                  · linarith only [h0, h432, hlam]
                  · linarith only [h432, h9, hlam]
                · linarith only [h431, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                rcases p423_3 (m.d 0 2) (by simp) with h436 | h436
                · rcases p423_3 (m.d 1 2) (by simp) with h437 | h437
                  · linarith only [h0, h437, hlam]
                  · linarith only [h10, h437, hlam]
                · linarith only [h436, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h0, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                rcases p423_3 (m.d 0 2) (by simp) with h443 | h443
                · rcases p423_3 (m.d 1 2) (by simp) with h444 | h444
                  · rcases p423_3 (m.d 2 3) (by simp) with h445 | h445
                    · linarith only [h445, hlam, p423_0]
                    · rcases p423_3 (m.d 2 4) (by simp) with h447 | h447
                      · linarith only [h447, h9, hlam]
                      · linarith only [h417, h447, hlam]
                  · linarith only [h444, hlam, p423_0]
                · linarith only [h3, h443, hlam]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h0, h421, hc01, hc45, hlam, hphi, ht0b, ht5b, p423_1]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                rcases p423_3 (m.d 0 2) (by simp) with h453 | h453
                · rcases p423_3 (m.d 1 2) (by simp) with h454 | h454
                  · rcases p423_3 (m.d 2 3) (by simp) with h455 | h455
                    · linarith only [h455, h8, hlam]
                    · rcases p423_3 (m.d 2 4) (by simp) with h457 | h457
                      · linarith only [h457, h9, hlam]
                      · linarith only [h421, h457, hlam]
                  · linarith only [h454, hlam, p423_0]
                · linarith only [h453, h5, hlam]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h3, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h8, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h417, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h419, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h4, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h9, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h0, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p423_1]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h5, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h10, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [h421, hlam, p423_0]
              · have p423_0 := h423c.1
                have p423_1 := h423c.2.1
                have p423_2 := h423c.2.2.1
                have p423_3 := h423c.2.2.2
                linarith only [hlam, p423_0]
            · linarith only [h11, h416, h422, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h478 | h478
            · rcases h2bigk with h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c | h479c
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h0, h416, h417, h421, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p479_1]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h11, h3, h416, h417, h421, h6, hlam, p479_2]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h11, h3, h416, h421, h6, hlam, p479_2]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                rcases p479_3 (m.d 0 2) (by simp) with h484 | h484
                · rcases p479_3 (m.d 1 2) (by simp) with h485 | h485
                  · linarith only [h0, h485, hlam]
                  · linarith only [h10, h485, hlam]
                · linarith only [h484, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h0, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                rcases p479_3 (m.d 0 2) (by simp) with h491 | h491
                · rcases p479_3 (m.d 1 2) (by simp) with h492 | h492
                  · rcases p479_3 (m.d 2 3) (by simp) with h493 | h493
                    · linarith only [h493, hlam, p479_0]
                    · rcases p479_3 (m.d 2 4) (by simp) with h495 | h495
                      · linarith only [h495, h9, hlam]
                      · linarith only [h417, h495, hlam]
                  · linarith only [h492, hlam, p479_0]
                · linarith only [h3, h491, hlam]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                rcases p479_3 (m.d 0 2) (by simp) with h500 | h500
                · rcases p479_3 (m.d 1 2) (by simp) with h501 | h501
                  · rcases p479_3 (m.d 2 3) (by simp) with h502 | h502
                    · linarith only [h502, h8, hlam]
                    · rcases p479_3 (m.d 2 4) (by simp) with h504 | h504
                      · linarith only [h504, hlam, p479_0]
                      · rcases p479_3 (m.d 2 5) (by simp) with h506 | h506
                        · linarith only [h10, h506, hlam]
                        · linarith only [h421, h506, hlam]
                  · linarith only [h501, hlam, p479_0]
                · linarith only [h4, h500, hlam]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                rcases p479_3 (m.d 0 2) (by simp) with h511 | h511
                · rcases p479_3 (m.d 1 2) (by simp) with h512 | h512
                  · rcases p479_3 (m.d 2 3) (by simp) with h513 | h513
                    · linarith only [h513, h8, hlam]
                    · rcases p479_3 (m.d 2 4) (by simp) with h515 | h515
                      · linarith only [h515, h9, hlam]
                      · rcases p479_3 (m.d 2 5) (by simp) with h517 | h517
                        · linarith only [h517, hlam, p479_0]
                        · rcases h4bigk with h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h0, h3, h416, h417, h421, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            rcases p519_3 (m.d 0 4) (by simp) with h522 | h522
                            · rcases p519_3 (m.d 1 4) (by simp) with h523 | h523
                              · linarith only [h2, h523, hlam]
                              · linarith only [h523, h9, hlam]
                            · linarith only [h4, h522, hlam]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h11, h416, h417, h421, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            rcases p519_3 (m.d 0 4) (by simp) with h528 | h528
                            · rcases p519_3 (m.d 1 4) (by simp) with h529 | h529
                              · linarith only [h2, h529, hlam]
                              · linarith only [h416, h529, hlam]
                            · linarith only [h528, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h2, hlam, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            rcases p519_3 (m.d 0 4) (by simp) with h535 | h535
                            · rcases p519_3 (m.d 1 4) (by simp) with h536 | h536
                              · rcases p519_3 (m.d 2 4) (by simp) with h537 | h537
                                · linarith only [h537, h9, hlam]
                                · rcases p519_3 (m.d 3 4) (by simp) with h539 | h539
                                  · rcases p519_3 (m.d 4 5) (by simp) with h540 | h540
                                    · linarith only [h416, h540, hlam]
                                    · linarith only [h421, h540, hlam]
                                  · linarith only [h417, h539, hlam]
                              · linarith only [h536, h9, hlam]
                            · linarith only [h4, h535, hlam]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h11, hlam, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h11, h417, h421, hc23, hc34, hlam, hphi, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h4, hlam, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h9, hlam, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h417, hlam, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h421, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h6, hlam, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h0, h3, h416, h417, h421, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            rcases p519_3 (m.d 0 4) (by simp) with h555 | h555
                            · rcases p519_3 (m.d 1 4) (by simp) with h556 | h556
                              · linarith only [h11, h556, hlam]
                              · linarith only [h556, h9, hlam]
                            · linarith only [h4, h555, hlam]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h0, h3, h417, h421, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h7, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h416, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h2, h416, h417, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p519_1]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [h478, hlam, p519_0]
                          · have p519_0 := h519c.1
                            have p519_1 := h519c.2.1
                            have p519_2 := h519c.2.2.1
                            have p519_3 := h519c.2.2.2
                            linarith only [hlam, p519_0]
                  · linarith only [h512, hlam, p479_0]
                · linarith only [h5, h511, hlam]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h3, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h8, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h417, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h419, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h4, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h9, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p479_1]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h421, hlam, p479_1]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h5, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h10, hlam, p479_0]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p479_1]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p479_1]
              · have p479_0 := h479c.1
                have p479_1 := h479c.2.1
                have p479_2 := h479c.2.2.1
                have p479_3 := h479c.2.2.2
                linarith only [hlam, p479_0]
            · linarith only [h11, h416, h478, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h585 | h585
      · linarith only [h11, h585, h8, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h587 | h587
        · linarith only [h0, h361, h587, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h589 | h589
          · linarith only [h416, h589, h9, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h591 | h591
            · rcases h2bigk with h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 2) (by simp) with h594 | h594
                · rcases p592_3 (m.d 1 2) (by simp) with h595 | h595
                  · linarith only [h0, h595, hlam]
                  · rcases p592_3 (m.d 2 3) (by simp) with h597 | h597
                    · linarith only [h3, h597, hlam]
                    · rcases p592_3 (m.d 2 4) (by simp) with h599 | h599
                      · linarith only [h4, h599, hlam]
                      · rcases p592_3 (m.d 2 5) (by simp) with h601 | h601
                        · linarith only [h5, h601, hlam]
                        · rcases h4bigk with h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [hlam, p603_0]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            rcases p603_3 (m.d 0 4) (by simp) with h605 | h605
                            · rcases p603_3 (m.d 1 4) (by simp) with h606 | h606
                              · linarith only [h2, h606, hlam]
                              · rcases p603_3 (m.d 2 4) (by simp) with h608 | h608
                                · linarith only [h4, h608, hlam]
                                · rcases p603_3 (m.d 3 4) (by simp) with h610 | h610
                                  · linarith only [h6, h610, hlam]
                                  · linarith only [h11, h610, hlam]
                            · linarith only [h2, h605, hlam]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            rcases p603_3 (m.d 0 4) (by simp) with h614 | h614
                            · rcases p603_3 (m.d 1 4) (by simp) with h615 | h615
                              · linarith only [h2, h615, hlam]
                              · linarith only [h615, h9, hlam]
                            · linarith only [h4, h614, hlam]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h416, h591, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            rcases p603_3 (m.d 0 4) (by simp) with h620 | h620
                            · rcases p603_3 (m.d 1 4) (by simp) with h621 | h621
                              · linarith only [h2, h621, hlam]
                              · rcases p603_3 (m.d 2 4) (by simp) with h623 | h623
                                · linarith only [h4, h623, hlam]
                                · rcases p603_3 (m.d 3 4) (by simp) with h625 | h625
                                  · linarith only [h6, h625, hlam]
                                  · linarith only [h591, h625, hlam]
                            · linarith only [h620, hlam, p603_0]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h2, hlam, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [hlam, p603_0]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h416, h585, h591, hc23, hc34, hlam, hphi, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h11, hlam, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h416, hlam, p603_0]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h4, hlam, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h9, hlam, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [hlam, p603_0]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h585, hlam, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h589, hlam, p603_0]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h6, hlam, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            rcases p603_3 (m.d 0 4) (by simp) with h640 | h640
                            · rcases p603_3 (m.d 1 4) (by simp) with h641 | h641
                              · linarith only [h11, h641, hlam]
                              · rcases p603_3 (m.d 2 4) (by simp) with h643 | h643
                                · linarith only [h585, h643, hlam]
                                · rcases p603_3 (m.d 3 4) (by simp) with h645 | h645
                                  · rcases p603_3 (m.d 4 5) (by simp) with h646 | h646
                                    · linarith only [h591, h646, hlam]
                                    · linarith only [h416, h646, hlam]
                                  · linarith only [h11, h645, hlam]
                            · linarith only [h2, h640, hlam]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            rcases p603_3 (m.d 0 4) (by simp) with h651 | h651
                            · rcases p603_3 (m.d 1 4) (by simp) with h652 | h652
                              · linarith only [h11, h652, hlam]
                              · linarith only [h652, h9, hlam]
                            · linarith only [h4, h651, hlam]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [hlam, p603_0]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h0, h3, h416, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h7, hlam, p603_0]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h0, h3, h585, h591, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h0, h3, h585, h591, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p603_1]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [h591, hlam, p603_0]
                          · have p603_0 := h603c.1
                            have p603_1 := h603c.2.1
                            have p603_2 := h603c.2.2.1
                            have p603_3 := h603c.2.2.2
                            linarith only [hlam, p603_0]
                · linarith only [h0, h594, hlam]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h3, h416, h585, h591, h6, h9, hlam, p592_2]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h3, h416, h591, h6, h9, hlam, p592_2]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 2) (by simp) with h666 | h666
                · rcases p592_3 (m.d 1 2) (by simp) with h667 | h667
                  · linarith only [h0, h667, hlam]
                  · linarith only [h10, h667, hlam]
                · linarith only [h666, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h0, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 2) (by simp) with h673 | h673
                · rcases p592_3 (m.d 1 2) (by simp) with h674 | h674
                  · rcases p592_3 (m.d 2 3) (by simp) with h675 | h675
                    · linarith only [h675, hlam, p592_0]
                    · rcases p592_3 (m.d 2 4) (by simp) with h677 | h677
                      · linarith only [h677, h9, hlam]
                      · linarith only [h585, h677, hlam]
                  · linarith only [h674, hlam, p592_0]
                · linarith only [h3, h673, hlam]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 2) (by simp) with h682 | h682
                · rcases p592_3 (m.d 1 2) (by simp) with h683 | h683
                  · rcases p592_3 (m.d 2 3) (by simp) with h684 | h684
                    · linarith only [h684, h8, hlam]
                    · rcases p592_3 (m.d 2 4) (by simp) with h686 | h686
                      · linarith only [h686, hlam, p592_0]
                      · rcases p592_3 (m.d 2 5) (by simp) with h688 | h688
                        · linarith only [h10, h688, hlam]
                        · linarith only [h589, h688, hlam]
                  · linarith only [h683, hlam, p592_0]
                · linarith only [h4, h682, hlam]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                rcases p592_3 (m.d 0 2) (by simp) with h693 | h693
                · rcases p592_3 (m.d 1 2) (by simp) with h694 | h694
                  · rcases p592_3 (m.d 2 3) (by simp) with h695 | h695
                    · linarith only [h695, h8, hlam]
                    · rcases p592_3 (m.d 2 4) (by simp) with h697 | h697
                      · linarith only [h697, h9, hlam]
                      · rcases p592_3 (m.d 2 5) (by simp) with h699 | h699
                        · linarith only [h699, hlam, p592_0]
                        · rcases h4bigk with h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            rcases p701_3 (m.d 0 4) (by simp) with h703 | h703
                            · rcases p701_3 (m.d 1 4) (by simp) with h704 | h704
                              · linarith only [h2, h704, hlam]
                              · rcases p701_3 (m.d 2 4) (by simp) with h706 | h706
                                · linarith only [h4, h706, hlam]
                                · rcases p701_3 (m.d 3 4) (by simp) with h708 | h708
                                  · linarith only [h6, h708, hlam]
                                  · linarith only [h11, h708, hlam]
                            · linarith only [h2, h703, hlam]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            rcases p701_3 (m.d 0 4) (by simp) with h712 | h712
                            · rcases p701_3 (m.d 1 4) (by simp) with h713 | h713
                              · linarith only [h2, h713, hlam]
                              · linarith only [h713, h9, hlam]
                            · linarith only [h4, h712, hlam]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h416, h591, hc04, hc14, hlam, hphi, ht0b, ht45, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            rcases p701_3 (m.d 0 4) (by simp) with h718 | h718
                            · rcases p701_3 (m.d 1 4) (by simp) with h719 | h719
                              · linarith only [h2, h719, hlam]
                              · rcases p701_3 (m.d 2 4) (by simp) with h721 | h721
                                · linarith only [h4, h721, hlam]
                                · rcases p701_3 (m.d 3 4) (by simp) with h723 | h723
                                  · linarith only [h6, h723, hlam]
                                  · linarith only [h591, h723, hlam]
                            · linarith only [h718, hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h2, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h416, h585, h591, hc23, hc34, hlam, hphi, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h11, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h416, hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h4, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h9, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h585, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h589, hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h6, hlam, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            rcases p701_3 (m.d 0 4) (by simp) with h738 | h738
                            · rcases p701_3 (m.d 1 4) (by simp) with h739 | h739
                              · linarith only [h11, h739, hlam]
                              · rcases p701_3 (m.d 2 4) (by simp) with h741 | h741
                                · linarith only [h585, h741, hlam]
                                · rcases p701_3 (m.d 3 4) (by simp) with h743 | h743
                                  · rcases p701_3 (m.d 4 5) (by simp) with h744 | h744
                                    · linarith only [h591, h744, hlam]
                                    · linarith only [h416, h744, hlam]
                                  · linarith only [h11, h743, hlam]
                            · linarith only [h2, h738, hlam]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            rcases p701_3 (m.d 0 4) (by simp) with h749 | h749
                            · rcases p701_3 (m.d 1 4) (by simp) with h750 | h750
                              · linarith only [h11, h750, hlam]
                              · linarith only [h750, h9, hlam]
                            · linarith only [h4, h749, hlam]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h0, h3, h416, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h7, hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h0, h3, h585, h591, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h0, h3, h585, h591, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [h591, hlam, p701_0]
                          · have p701_0 := h701c.1
                            have p701_1 := h701c.2.1
                            have p701_2 := h701c.2.2.1
                            have p701_3 := h701c.2.2.2
                            linarith only [hlam, p701_0]
                  · linarith only [h694, hlam, p592_0]
                · linarith only [h5, h693, hlam]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h3, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h8, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h585, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h587, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h4, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h9, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p592_1]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h589, hlam, p592_1]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h5, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h10, hlam, p592_0]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p592_1]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [h0, h10, h3, h416, h591, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p592_1]
              · have p592_0 := h592c.1
                have p592_1 := h592c.2.1
                have p592_2 := h592c.2.2.1
                have p592_3 := h592c.2.2.2
                linarith only [hlam, p592_0]
            · rcases h2bigk with h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                rcases p778_3 (m.d 0 2) (by simp) with h780 | h780
                · rcases p778_3 (m.d 1 2) (by simp) with h781 | h781
                  · linarith only [h0, h781, hlam]
                  · rcases p778_3 (m.d 2 3) (by simp) with h783 | h783
                    · linarith only [h3, h783, hlam]
                    · rcases p778_3 (m.d 2 4) (by simp) with h785 | h785
                      · linarith only [h4, h785, hlam]
                      · rcases p778_3 (m.d 2 5) (by simp) with h787 | h787
                        · linarith only [h5, h787, hlam]
                        · rcases h4bigk with h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [hlam, p789_0]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            rcases p789_3 (m.d 0 4) (by simp) with h791 | h791
                            · rcases p789_3 (m.d 1 4) (by simp) with h792 | h792
                              · linarith only [h2, h792, hlam]
                              · rcases p789_3 (m.d 2 4) (by simp) with h794 | h794
                                · linarith only [h4, h794, hlam]
                                · rcases p789_3 (m.d 3 4) (by simp) with h796 | h796
                                  · linarith only [h6, h796, hlam]
                                  · linarith only [h11, h796, hlam]
                            · linarith only [h2, h791, hlam]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            rcases p789_3 (m.d 0 4) (by simp) with h800 | h800
                            · rcases p789_3 (m.d 1 4) (by simp) with h801 | h801
                              · linarith only [h2, h801, hlam]
                              · linarith only [h801, h9, hlam]
                            · linarith only [h4, h800, hlam]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            rcases p789_3 (m.d 0 4) (by simp) with h805 | h805
                            · rcases p789_3 (m.d 1 4) (by simp) with h806 | h806
                              · linarith only [h2, h806, hlam]
                              · rcases p789_3 (m.d 2 4) (by simp) with h808 | h808
                                · linarith only [h4, h808, hlam]
                                · rcases p789_3 (m.d 3 4) (by simp) with h810 | h810
                                  · linarith only [h6, h810, hlam]
                                  · rcases p789_3 (m.d 4 5) (by simp) with h812 | h812
                                    · linarith only [h7, h812, hlam]
                                    · linarith only [h591, h812, hlam]
                            · linarith only [h6, h805, hlam]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h0, h11, h3, h591, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h2, hlam, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [hlam, p789_0]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h0, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p778_1, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h11, hlam, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h416, hlam, p789_0]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h4, hlam, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h9, hlam, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [hlam, p789_0]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h585, hlam, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h589, hlam, p789_0]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h6, hlam, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h591, hc14, hc45, hlam, hphi, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h0, h3, h591, h6, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [hlam, p789_0]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h591, hlam, p789_0]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h7, hlam, p789_0]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            rcases p789_3 (m.d 0 4) (by simp) with h833 | h833
                            · rcases p789_3 (m.d 1 4) (by simp) with h834 | h834
                              · linarith only [h834, hlam, p789_0]
                              · rcases p789_3 (m.d 2 4) (by simp) with h836 | h836
                                · linarith only [h589, h836, hlam]
                                · rcases p789_3 (m.d 3 4) (by simp) with h838 | h838
                                  · linarith only [h591, h838, hlam]
                                  · linarith only [h11, h838, hlam]
                            · linarith only [h2, h833, hlam]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            rcases p789_3 (m.d 0 4) (by simp) with h842 | h842
                            · rcases p789_3 (m.d 1 4) (by simp) with h843 | h843
                              · linarith only [h416, h843, hlam]
                              · linarith only [h843, h9, hlam]
                            · linarith only [h4, h842, hlam]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [h0, h11, h3, h6, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p789_1]
                          · have p789_0 := h789c.1
                            have p789_1 := h789c.2.1
                            have p789_2 := h789c.2.2.1
                            have p789_3 := h789c.2.2.2
                            linarith only [hlam, p789_0]
                · linarith only [h0, h780, hlam]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h11, h3, h591, h6, h7, h8, hlam, p778_2]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                rcases p778_3 (m.d 0 2) (by simp) with h851 | h851
                · rcases p778_3 (m.d 1 2) (by simp) with h852 | h852
                  · linarith only [h0, h852, hlam]
                  · linarith only [h852, h9, hlam]
                · linarith only [h851, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                rcases p778_3 (m.d 0 2) (by simp) with h856 | h856
                · rcases p778_3 (m.d 1 2) (by simp) with h857 | h857
                  · linarith only [h0, h857, hlam]
                  · linarith only [h10, h857, hlam]
                · linarith only [h856, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h0, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                rcases p778_3 (m.d 0 2) (by simp) with h863 | h863
                · rcases p778_3 (m.d 1 2) (by simp) with h864 | h864
                  · rcases p778_3 (m.d 2 3) (by simp) with h865 | h865
                    · linarith only [h865, hlam, p778_0]
                    · rcases p778_3 (m.d 2 4) (by simp) with h867 | h867
                      · linarith only [h867, h9, hlam]
                      · linarith only [h585, h867, hlam]
                  · linarith only [h864, hlam, p778_0]
                · linarith only [h3, h863, hlam]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                rcases p778_3 (m.d 0 2) (by simp) with h872 | h872
                · rcases p778_3 (m.d 1 2) (by simp) with h873 | h873
                  · rcases p778_3 (m.d 2 3) (by simp) with h874 | h874
                    · linarith only [h8, h874, hlam]
                    · rcases p778_3 (m.d 2 4) (by simp) with h876 | h876
                      · linarith only [h876, hlam, p778_0]
                      · rcases p778_3 (m.d 2 5) (by simp) with h878 | h878
                        · linarith only [h10, h878, hlam]
                        · linarith only [h589, h878, hlam]
                  · linarith only [h873, hlam, p778_0]
                · linarith only [h4, h872, hlam]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                rcases p778_3 (m.d 0 2) (by simp) with h883 | h883
                · rcases p778_3 (m.d 1 2) (by simp) with h884 | h884
                  · rcases p778_3 (m.d 2 3) (by simp) with h885 | h885
                    · linarith only [h8, h885, hlam]
                    · rcases p778_3 (m.d 2 4) (by simp) with h887 | h887
                      · linarith only [h887, h9, hlam]
                      · rcases p778_3 (m.d 2 5) (by simp) with h889 | h889
                        · linarith only [h889, hlam, p778_0]
                        · rcases h4bigk with h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c | h891c
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [hlam, p891_0]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            rcases p891_3 (m.d 0 4) (by simp) with h893 | h893
                            · rcases p891_3 (m.d 1 4) (by simp) with h894 | h894
                              · linarith only [h2, h894, hlam]
                              · rcases p891_3 (m.d 2 4) (by simp) with h896 | h896
                                · linarith only [h4, h896, hlam]
                                · rcases p891_3 (m.d 3 4) (by simp) with h898 | h898
                                  · linarith only [h6, h898, hlam]
                                  · linarith only [h11, h898, hlam]
                            · linarith only [h2, h893, hlam]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            rcases p891_3 (m.d 0 4) (by simp) with h902 | h902
                            · rcases p891_3 (m.d 1 4) (by simp) with h903 | h903
                              · linarith only [h2, h903, hlam]
                              · linarith only [h9, h903, hlam]
                            · linarith only [h4, h902, hlam]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            rcases p891_3 (m.d 0 4) (by simp) with h907 | h907
                            · rcases p891_3 (m.d 1 4) (by simp) with h908 | h908
                              · linarith only [h2, h908, hlam]
                              · rcases p891_3 (m.d 2 4) (by simp) with h910 | h910
                                · linarith only [h4, h910, hlam]
                                · rcases p891_3 (m.d 3 4) (by simp) with h912 | h912
                                  · linarith only [h6, h912, hlam]
                                  · rcases p891_3 (m.d 4 5) (by simp) with h914 | h914
                                    · linarith only [h7, h914, hlam]
                                    · linarith only [h591, h914, hlam]
                            · linarith only [h6, h907, hlam]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h0, h11, h3, h591, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h2, hlam, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [hlam, p891_0]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h11, h591, hc24, hc45, hlam, hphi, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h11, hlam, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h416, hlam, p891_0]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h4, hlam, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h9, hlam, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [hlam, p891_0]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h585, hlam, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h589, hlam, p891_0]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h6, hlam, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h591, hc14, hc45, hlam, hphi, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h0, h3, h591, h6, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [hlam, p891_0]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h591, hlam, p891_0]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h7, hlam, p891_0]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            rcases p891_3 (m.d 0 4) (by simp) with h935 | h935
                            · rcases p891_3 (m.d 1 4) (by simp) with h936 | h936
                              · linarith only [h936, hlam, p891_0]
                              · rcases p891_3 (m.d 2 4) (by simp) with h938 | h938
                                · linarith only [h589, h938, hlam]
                                · rcases p891_3 (m.d 3 4) (by simp) with h940 | h940
                                  · linarith only [h591, h940, hlam]
                                  · linarith only [h11, h940, hlam]
                            · linarith only [h2, h935, hlam]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            rcases p891_3 (m.d 0 4) (by simp) with h944 | h944
                            · rcases p891_3 (m.d 1 4) (by simp) with h945 | h945
                              · linarith only [h416, h945, hlam]
                              · linarith only [h9, h945, hlam]
                            · linarith only [h4, h944, hlam]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [h0, h11, h3, h6, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p891_1]
                          · have p891_0 := h891c.1
                            have p891_1 := h891c.2.1
                            have p891_2 := h891c.2.2.1
                            have p891_3 := h891c.2.2.2
                            linarith only [hlam, p891_0]
                  · linarith only [h884, hlam, p778_0]
                · linarith only [h5, h883, hlam]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h3, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h8, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h585, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h587, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h4, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h9, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h589, hlam, p778_1]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h5, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h10, hlam, p778_0]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p778_1]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p778_1]
              · have p778_0 := h778c.1
                have p778_1 := h778c.2.1
                have p778_2 := h778c.2.2.1
                have p778_3 := h778c.2.2.2
                linarith only [hlam, p778_0]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
  · rcases m.htr 1 3 5 (by decide) (by decide) with h969 | h969
    · linarith only [h10, h8, h969, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h971 | h971
      · linarith only [h10, h8, h968, h971, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h973 | h973
        · linarith only [h0, h10, h5, h8, h973, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h968, h969, h973, hc23, hc35, hlam, hphi]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h976 | h976
    · linarith only [h10, h9, h968, h976, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h978 | h978
      · linarith only [h10, h9, h978, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h980 | h980
        · linarith only [h0, h10, h5, h8, h968, h980, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h982 | h982
          · linarith only [h10, h8, h976, h982, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h984 | h984
            · linarith only [h0, h10, h5, h9, h984, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h986 | h986
              · linarith only [h0, h10, h3, h6, h9, h980, h984, h986, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases h2bigk with h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  rcases p988_3 (m.d 0 2) (by simp) with h990 | h990
                  · rcases p988_3 (m.d 1 2) (by simp) with h991 | h991
                    · linarith only [h0, h991, hlam]
                    · rcases p988_3 (m.d 2 3) (by simp) with h993 | h993
                      · linarith only [h3, h993, hlam]
                      · rcases p988_3 (m.d 2 4) (by simp) with h995 | h995
                        · linarith only [h4, h995, hlam]
                        · rcases p988_3 (m.d 2 5) (by simp) with h997 | h997
                          · linarith only [h5, h997, hlam]
                          · linarith only [h10, h997, hlam]
                  · linarith only [h0, h990, hlam]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h10, h5, h9, h980, hlam, p988_2]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h10, h5, h9, hlam, p988_2]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h0, h10, h9, h980, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p988_1]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h0, hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h10, h982, hc23, hc35, hlam, hphi, p988_1]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h0, h10, h5, h980, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p988_1]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h10, hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h3, hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h8, hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h980, hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h982, hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h4, hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h9, hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h0, h10, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p988_1]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h984, hlam, p988_1]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h5, hlam, p988_0]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [h0, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p988_1]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  rcases p988_3 (m.d 0 2) (by simp) with h1021 | h1021
                  · rcases p988_3 (m.d 1 2) (by simp) with h1022 | h1022
                    · linarith only [h10, h1022, hlam]
                    · linarith only [h1022, h8, hlam]
                  · linarith only [h1021, h3, hlam]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  rcases p988_3 (m.d 0 2) (by simp) with h1026 | h1026
                  · rcases p988_3 (m.d 1 2) (by simp) with h1027 | h1027
                    · linarith only [h10, h1027, hlam]
                    · linarith only [h1027, h9, hlam]
                  · linarith only [h1026, h4, hlam]
                · have p988_0 := h988c.1
                  have p988_1 := h988c.2.1
                  have p988_2 := h988c.2.2.1
                  have p988_3 := h988c.2.2.2
                  linarith only [hlam, p988_0]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h1032 | h1032
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1033 | h1033
    · linarith only [h1033, h8, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1035 | h1035
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1036 | h1036
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1037 | h1037
          · linarith only [h0, h1033, h1035, h1037, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1039 | h1039
            · linarith only [h0, h1037, h1039, h3, h6, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h1035, h1037, h1039, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h1035, h1036, h8, h9, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1043 | h1043
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1044 | h1044
          · linarith only [h0, h1044, h4, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1046 | h1046
            · linarith only [h1035, h1046, h8, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1048 | h1048
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1049 | h1049
                · rcases h2bigk with h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    rcases p1050_3 (m.d 0 2) (by simp) with h1052 | h1052
                    · rcases p1050_3 (m.d 1 2) (by simp) with h1053 | h1053
                      · linarith only [h0, h1053, hlam]
                      · rcases p1050_3 (m.d 2 3) (by simp) with h1055 | h1055
                        · linarith only [h1055, h3, hlam]
                        · rcases p1050_3 (m.d 2 4) (by simp) with h1057 | h1057
                          · linarith only [h1057, h4, hlam]
                          · linarith only [h1057, h9, hlam]
                    · linarith only [h0, h1052, hlam]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h1044, h3, h6, h8, h9, hlam, p1050_2]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h0, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1050_1]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h1032, h4, h9, hlam, p1050_2]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h0, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h0, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1050_1]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h9, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h0, h4, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p1050_1]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h3, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h8, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h1044, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h1046, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h4, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1050_1]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    rcases p1050_3 (m.d 0 2) (by simp) with h1076 | h1076
                    · rcases p1050_3 (m.d 1 2) (by simp) with h1077 | h1077
                      · linarith only [h1077, h9, hlam]
                      · linarith only [h1077, h8, hlam]
                    · linarith only [h1076, h3, hlam]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    rcases p1050_3 (m.d 0 2) (by simp) with h1082 | h1082
                    · rcases p1050_3 (m.d 1 2) (by simp) with h1083 | h1083
                      · linarith only [h1083, h9, hlam]
                      · linarith only [h1032, h1083, hlam]
                    · linarith only [h1082, h5, hlam]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h5, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h1032, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h0, h1032, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1050_1]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [h1048, hlam, p1050_0]
                  · have p1050_0 := h1050c.1
                    have p1050_1 := h1050c.2.1
                    have p1050_2 := h1050c.2.2.1
                    have p1050_3 := h1050c.2.2.2
                    linarith only [hlam, p1050_0]
                · linarith only [h0, h1032, h1044, h1049, h3, h6, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h1032, h1046, h1048, h9, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h1032, h1043, h9, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1095 | h1095
    · linarith only [h1095, h8, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1097 | h1097
      · linarith only [h1032, h1097, h8, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1099 | h1099
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1100 | h1100
          · linarith only [h1095, h1100, h8, h9, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1102 | h1102
            · linarith only [h1032, h1097, h1102, h8, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1104 | h1104
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1105 | h1105
                · rcases h2bigk with h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c | h1106c
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    rcases p1106_3 (m.d 0 2) (by simp) with h1108 | h1108
                    · rcases p1106_3 (m.d 1 2) (by simp) with h1109 | h1109
                      · linarith only [h0, h1109, hlam]
                      · rcases p1106_3 (m.d 2 3) (by simp) with h1111 | h1111
                        · linarith only [h1111, h3, hlam]
                        · rcases p1106_3 (m.d 2 4) (by simp) with h1113 | h1113
                          · linarith only [h1113, h4, hlam]
                          · linarith only [h1113, h9, hlam]
                    · linarith only [h0, h1108, hlam]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h1032, h1100, h1104, h3, h6, h8, hlam, p1106_2]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h0, h1032, h1104, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1106_1]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h0, h1032, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1106_1]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h0, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h1032, h1100, h1104, hc23, hc34, hlam, hphi, p1106_1]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h9, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h1032, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h3, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h8, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h1100, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h1102, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h4, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1106_1]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    rcases p1106_3 (m.d 0 2) (by simp) with h1132 | h1132
                    · rcases p1106_3 (m.d 1 2) (by simp) with h1133 | h1133
                      · linarith only [h1133, h9, hlam]
                      · linarith only [h1133, h8, hlam]
                    · linarith only [h1132, h3, hlam]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h0, h1032, h1100, h3, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1106_1]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h5, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h1102, h8, hc23, hc35, hlam, hphi, p1106_1]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    rcases p1106_3 (m.d 0 2) (by simp) with h1141 | h1141
                    · rcases p1106_3 (m.d 1 2) (by simp) with h1142 | h1142
                      · linarith only [h1032, h1142, hlam]
                      · linarith only [h1142, h8, hlam]
                    · linarith only [h1141, h3, hlam]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [h1104, hlam, p1106_0]
                  · have p1106_0 := h1106c.1
                    have p1106_1 := h1106c.2.1
                    have p1106_2 := h1106c.2.2.1
                    have p1106_3 := h1106c.2.2.2
                    linarith only [hlam, p1106_0]
                · linarith only [h0, h1100, h1105, h3, h6, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h1099, h1104, h8, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1150 | h1150
          · linarith only [h0, h1032, h1150, h5, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1152 | h1152
            · linarith only [h0, h1099, h1152, h3, h6, h7, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1154 | h1154
              · linarith only [h0, h1099, h1150, h1154, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h1154, h3, h6, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 4870000 in
set_option maxHeartbeats 4870000 in
theorem r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  · exact r1l7_20_12_14_H_R_L_I_L_I_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

end R2N4
