import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 4 (by decide) (by decide) with h351 | h351
  · rcases m.htr 1 2 5 (by decide) (by decide) with h352 | h352
    · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
      · rcases m.htr 1 4 5 (by decide) (by decide) with h354 | h354
        · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
          · rcases m.htr 2 3 5 (by decide) (by decide) with h356 | h356
            · rcases m.htr 2 4 5 (by decide) (by decide) with h357 | h357
              · linarith only [h0, h10, h351, h357, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h351, h354, h357, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h10, h356, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h0, h10, h351, h355, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h362 | h362
          · rcases m.htr 2 3 5 (by decide) (by decide) with h363 | h363
            · rcases m.htr 2 4 5 (by decide) (by decide) with h364 | h364
              · linarith only [h10, h351, h354, h364, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h366 | h366
                · linarith only [h351, h354, h362, h366, hlam]
                · rcases h0bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [hlam, p368_0]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h351, h354, h362, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h351, h354, h362, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
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
                    linarith only [h351, h354, h362, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h0, h351, h354, h362, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h0, h351, h354, h362, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h1, hlam, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h4, hlam, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [hlam, p368_0]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h351, h354, h362, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h0, h351, h354, h362, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h2, hlam, p368_0]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h5, hlam, p368_0]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h7, hlam, p368_0]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [hlam, p368_0]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h0, h351, h354, h362, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h3, hlam, p368_0]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h6, hlam, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h8, hlam, p368_0]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [h9, hlam, p368_1]
                  · have p368_0 := h368c.1
                    have p368_1 := h368c.2.1
                    have p368_2 := h368c.2.2.1
                    have p368_3 := h368c.2.2.2
                    linarith only [hlam, p368_0]
            · linarith only [h10, h351, h362, h363, hc34, hlam, hphi, ht45, u5elo3]
          · linarith only [h0, h10, h351, h362, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h351, h353, hlam]
    · linarith only [h351, h352, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
    · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
      · rcases m.htr 1 4 5 (by decide) (by decide) with h400 | h400
        · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
          · rcases m.htr 2 3 5 (by decide) (by decide) with h402 | h402
            · rcases m.htr 2 4 5 (by decide) (by decide) with h403 | h403
              · rcases m.htr 3 4 5 (by decide) (by decide) with h404 | h404
                · rcases h0bigk with h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h0, h398, h402, h404, hc01, hc45, hlam, hphi, ht0b, ht5b, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h1, h399, h404, hc01, hc45, hlam, hphi, ht0b, ht5b, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h2, h351, h398, h402, h404, hc01, hc45, hlam, hphi, ht0b, ht5b, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    rcases p405_3 (m.d 0 1) (by simp) with h410 | h410
                    · rcases p405_3 (m.d 0 2) (by simp) with h411 | h411
                      · linarith only [h0, h411, hlam]
                      · linarith only [h411, h6, hlam]
                    · linarith only [h3, h410, hlam]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h0, hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h351, h398, h4, h401, h402, h404, hc02, hc45, hlam, hphi, ht0b, ht5b, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h0, h351, h398, h402, h404, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    rcases p405_3 (m.d 0 1) (by simp) with h419 | h419
                    · rcases p405_3 (m.d 0 2) (by simp) with h420 | h420
                      · rcases p405_3 (m.d 0 3) (by simp) with h421 | h421
                        · linarith only [h4, h421, hlam]
                        · linarith only [h421, h8, hlam]
                      · linarith only [h420, h6, hlam]
                    · linarith only [h3, h419, hlam]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h1, hlam, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h4, hlam, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h351, h398, h402, h404, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    rcases p405_3 (m.d 0 1) (by simp) with h430 | h430
                    · rcases p405_3 (m.d 0 2) (by simp) with h431 | h431
                      · rcases p405_3 (m.d 0 3) (by simp) with h432 | h432
                        · rcases p405_3 (m.d 0 4) (by simp) with h433 | h433
                          · linarith only [h433, h7, hlam]
                          · linarith only [h433, h9, hlam]
                        · linarith only [h432, h8, hlam]
                      · linarith only [h431, h6, hlam]
                    · linarith only [h3, h430, hlam]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h2, hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h5, hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h7, hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    rcases p405_3 (m.d 0 1) (by simp) with h443 | h443
                    · rcases p405_3 (m.d 0 2) (by simp) with h444 | h444
                      · rcases p405_3 (m.d 0 3) (by simp) with h445 | h445
                        · rcases p405_3 (m.d 0 4) (by simp) with h446 | h446
                          · rcases p405_3 (m.d 0 5) (by simp) with h447 | h447
                            · linarith only [h447, h9, hlam]
                            · rcases h2bigk with h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                rcases p449_3 (m.d 0 2) (by simp) with h451 | h451
                                · rcases p449_3 (m.d 1 2) (by simp) with h452 | h452
                                  · linarith only [h0, h452, hlam]
                                  · rcases p449_3 (m.d 2 3) (by simp) with h454 | h454
                                    · linarith only [h4, h454, hlam]
                                    · linarith only [h10, h454, hlam]
                                · linarith only [h0, h451, hlam]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h0, h351, h398, h401, h402, h404, hc01, hc45, hlam, hphi, ht0b, ht5b, p449_1]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h0, h351, h398, h402, h404, hc01, hc45, hlam, hphi, ht0b, ht5b, p449_1]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h351, h398, h4, h401, hlam, p449_2]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h0, hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h10, hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h351, hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h351, h4, h401, h402, h404, hc02, hc45, hlam, hphi, ht0b, ht5b, p449_1]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h4, hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h0, h398, h4, h402, h404, hc01, hc45, hlam, hphi, ht0b, ht5b, p449_1]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h0, h351, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p449_1]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                rcases p449_3 (m.d 0 2) (by simp) with h470 | h470
                                · rcases p449_3 (m.d 1 2) (by simp) with h471 | h471
                                  · linarith only [h10, h471, hlam]
                                  · linarith only [h398, h471, hlam]
                                · linarith only [h470, h6, hlam]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h5, hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h0, h398, h402, h404, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p449_1]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h401, hlam, p449_1]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                rcases p449_3 (m.d 0 2) (by simp) with h479 | h479
                                · rcases p449_3 (m.d 1 2) (by simp) with h480 | h480
                                  · linarith only [h351, h480, hlam]
                                  · linarith only [h398, h480, hlam]
                                · linarith only [h479, h6, hlam]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h6, hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h398, hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h402, hlam, p449_1]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [h403, hlam, p449_0]
                              · have p449_0 := h449c.1
                                have p449_1 := h449c.2.1
                                have p449_2 := h449c.2.2.1
                                have p449_3 := h449c.2.2.2
                                linarith only [hlam, p449_0]
                          · linarith only [h446, h9, hlam]
                        · linarith only [h445, h8, hlam]
                      · linarith only [h444, h6, hlam]
                    · linarith only [h3, h443, hlam]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h3, hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h6, hlam, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h8, hlam, p405_0]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [h9, hlam, p405_1]
                  · have p405_0 := h405c.1
                    have p405_1 := h405c.2.1
                    have p405_2 := h405c.2.2.1
                    have p405_3 := h405c.2.2.2
                    linarith only [hlam, p405_0]
                · linarith only [h0, h10, h398, h4, h403, h404, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h351, h398, h399, h400, h403, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h10, h398, h402, h8, hc25, hlam, hphi, u5elo0]
          · linarith only [h0, h10, h398, h4, h401, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h351, h398, h400, h9, hc25, hlam, hphi, u5elo0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h503 | h503
        · rcases m.htr 2 3 4 (by decide) (by decide) with h504 | h504
          · linarith only [h0, h10, h398, h399, h4, h504, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h398, h4, h504, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h10, h398, h399, h503, hc25, hlam, hphi, u5elo4]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
      · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
        · rcases m.htr 2 3 4 (by decide) (by decide) with h510 | h510
          · rcases m.htr 2 3 5 (by decide) (by decide) with h511 | h511
            · rcases m.htr 2 4 5 (by decide) (by decide) with h512 | h512
              · rcases m.htr 3 4 5 (by decide) (by decide) with h513 | h513
                · rcases h0bigk with h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c | h514c
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h1, h4, h508, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h1, h508, h513, hc01, hc45, hlam, hphi, ht0b, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h513, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h398, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h0, hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h10, h4, h508, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h0, h351, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h0, h398, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h1, hlam, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h4, hlam, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h351, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h0, h398, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h2, hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h5, hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h7, hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h0, h398, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h3, hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h6, hlam, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h8, hlam, p514_0]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [h9, hlam, p514_1]
                  · have p514_0 := h514c.1
                    have p514_1 := h514c.2.1
                    have p514_2 := h514c.2.2.1
                    have p514_3 := h514c.2.2.2
                    linarith only [hlam, p514_0]
                · rcases h0bigk with h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c | h540c
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h1, h4, h508, h509, h513, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h1, h508, h509, h513, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h2, h509, h513, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h398, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h0, hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h1, h508, h509, h513, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h0, h2, h509, h513, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h0, h398, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h1, hlam, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h4, hlam, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h351, h5, h509, h513, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h0, h398, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h2, hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h5, hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h7, hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h398, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h3, hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h6, hlam, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h8, hlam, p540_0]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [h9, hlam, p540_1]
                  · have p540_0 := h540c.1
                    have p540_1 := h540c.2.1
                    have p540_2 := h540c.2.2.1
                    have p540_3 := h540c.2.2.2
                    linarith only [hlam, p540_0]
              · linarith only [h351, h509, h512, hlam]
            · linarith only [h10, h508, h509, h511, hc45, hlam, hphi, u5elo3]
          · linarith only [h1, h10, h508, h510, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h569 | h569
          · rcases m.htr 2 3 5 (by decide) (by decide) with h570 | h570
            · rcases m.htr 2 4 5 (by decide) (by decide) with h571 | h571
              · rcases m.htr 3 4 5 (by decide) (by decide) with h572 | h572
                · linarith only [h508, h509, h572, hlam]
                · rcases h0bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h10, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h4, h508, h509, h569, h571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h5, h508, h509, h571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h508, h509, h571, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h0, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h4, h508, h509, h569, h571, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h0, h5, h508, h509, h571, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h0, h508, h509, h571, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h1, hlam, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h4, hlam, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h5, h508, h509, h571, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h0, h4, h508, h509, h571, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h2, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h5, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h7, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h508, h509, h571, h6, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h3, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h6, hlam, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h8, hlam, p574_0]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [h9, hlam, p574_1]
                  · have p574_0 := h574c.1
                    have p574_1 := h574c.2.1
                    have p574_2 := h574c.2.2.1
                    have p574_3 := h574c.2.2.2
                    linarith only [hlam, p574_0]
              · linarith only [h351, h571, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
            · linarith only [h351, h569, h570, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h10, h508, h569, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h603 | h603
        · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
          · rcases m.htr 2 3 5 (by decide) (by decide) with h605 | h605
            · rcases m.htr 2 4 5 (by decide) (by decide) with h606 | h606
              · rcases m.htr 3 4 5 (by decide) (by decide) with h607 | h607
                · rcases h0bigk with h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c | h608c
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h4, h508, h604, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h4, h508, h604, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h508, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h398, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h0, hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h4, h508, h604, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h0, h508, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h0, h398, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h1, hlam, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h4, hlam, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h508, h7, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h0, h398, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h2, hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h5, hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h7, hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h398, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h3, hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h6, hlam, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h8, hlam, p608_0]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [h9, hlam, p608_1]
                  · have p608_0 := h608c.1
                    have p608_1 := h608c.2.1
                    have p608_2 := h608c.2.2.1
                    have p608_3 := h608c.2.2.2
                    linarith only [hlam, p608_0]
                · linarith only [h508, h603, h607, hlam]
              · linarith only [h0, h4, h508, h603, h604, h606, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h508, h604, h605, hc14, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h637 | h637
            · rcases m.htr 2 4 5 (by decide) (by decide) with h638 | h638
              · rcases m.htr 3 4 5 (by decide) (by decide) with h639 | h639
                · rcases h0bigk with h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h398, h4, h604, h637, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h398, h604, h637, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h2, h603, hc01, hc45, hlam, hphi, ht0b, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h398, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h0, hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h398, h604, h637, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h0, h2, h603, hc01, hc45, hlam, hphi, ht0b, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h0, h398, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h1, hlam, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h4, hlam, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h2, h603, hc03, hc45, hlam, hphi, ht0b, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h0, h398, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h2, hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h5, hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h7, hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h398, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h3, hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h6, hlam, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h8, hlam, p640_0]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [h9, hlam, p640_1]
                  · have p640_0 := h640c.1
                    have p640_1 := h640c.2.1
                    have p640_2 := h640c.2.2.1
                    have p640_3 := h640c.2.2.2
                    linarith only [hlam, p640_0]
                · linarith only [h351, h604, h639, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h398, h603, h604, h637, h638, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
            · linarith only [h10, h637, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h669 | h669
          · rcases m.htr 2 3 5 (by decide) (by decide) with h670 | h670
            · rcases m.htr 2 4 5 (by decide) (by decide) with h671 | h671
              · rcases m.htr 3 4 5 (by decide) (by decide) with h672 | h672
                · linarith only [h0, h4, h603, h669, h672, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h10, h508, h671, h672, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h351, h671, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
            · linarith only [h10, h670, h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h677 | h677
            · rcases m.htr 2 4 5 (by decide) (by decide) with h678 | h678
              · rcases m.htr 3 4 5 (by decide) (by decide) with h679 | h679
                · linarith only [h10, h508, h603, h669, h677, h679, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h669, h677, h678, h679, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h351, h678, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
            · linarith only [h10, h677, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9 h10
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9 h10

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h684 | h684
  · rcases m.htr 1 2 4 (by decide) (by decide) with h685 | h685
    · rcases m.htr 1 2 5 (by decide) (by decide) with h686 | h686
      · rcases m.htr 1 3 4 (by decide) (by decide) with h687 | h687
        · rcases m.htr 1 4 5 (by decide) (by decide) with h688 | h688
          · linarith only [h2, h688, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h690 | h690
            · rcases m.htr 2 3 5 (by decide) (by decide) with h691 | h691
              · rcases m.htr 2 4 5 (by decide) (by decide) with h692 | h692
                · linarith only [h5, h692, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
                  · linarith only [h694, h7, h9, hlam]
                  · rcases h0bigk with h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h0, h684, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p696_1]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h4, h691, h694, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p696_1]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      rcases p696_3 (m.d 0 1) (by simp) with h700 | h700
                      · rcases p696_3 (m.d 0 2) (by simp) with h701 | h701
                        · linarith only [h0, h701, hlam]
                        · linarith only [h5, h701, hlam]
                      · linarith only [h2, h700, hlam]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      rcases p696_3 (m.d 0 1) (by simp) with h705 | h705
                      · rcases p696_3 (m.d 0 2) (by simp) with h706 | h706
                        · linarith only [h0, h706, hlam]
                        · linarith only [h6, h706, hlam]
                      · linarith only [h3, h705, hlam]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h0, hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h1, h684, h691, h694, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p696_1]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      rcases p696_3 (m.d 0 1) (by simp) with h713 | h713
                      · rcases p696_3 (m.d 0 2) (by simp) with h714 | h714
                        · rcases p696_3 (m.d 0 3) (by simp) with h715 | h715
                          · linarith only [h4, h715, hlam]
                          · linarith only [h7, h715, hlam]
                        · linarith only [h5, h714, hlam]
                      · linarith only [h2, h713, hlam]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      rcases p696_3 (m.d 0 1) (by simp) with h720 | h720
                      · rcases p696_3 (m.d 0 2) (by simp) with h721 | h721
                        · rcases p696_3 (m.d 0 3) (by simp) with h722 | h722
                          · linarith only [h4, h722, hlam]
                          · linarith only [h722, h8, hlam]
                        · linarith only [h6, h721, hlam]
                      · linarith only [h3, h720, hlam]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h1, hlam, p696_1]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h4, hlam, p696_1]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      rcases p696_3 (m.d 0 1) (by simp) with h730 | h730
                      · rcases p696_3 (m.d 0 2) (by simp) with h731 | h731
                        · rcases p696_3 (m.d 0 3) (by simp) with h732 | h732
                          · rcases p696_3 (m.d 0 4) (by simp) with h733 | h733
                            · linarith only [h7, h733, hlam]
                            · rcases p696_3 (m.d 0 5) (by simp) with h735 | h735
                              · linarith only [h735, h8, hlam]
                              · linarith only [h735, h9, hlam]
                          · linarith only [h7, h732, hlam]
                        · linarith only [h5, h731, hlam]
                      · linarith only [h2, h730, hlam]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      rcases p696_3 (m.d 0 1) (by simp) with h741 | h741
                      · rcases p696_3 (m.d 0 2) (by simp) with h742 | h742
                        · rcases p696_3 (m.d 0 3) (by simp) with h743 | h743
                          · rcases p696_3 (m.d 0 4) (by simp) with h744 | h744
                            · linarith only [h7, h744, hlam]
                            · rcases p696_3 (m.d 0 5) (by simp) with h746 | h746
                              · linarith only [h746, h8, hlam]
                              · rcases h2bigk with h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c | h748c
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h0, h684, h691, h694, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p748_1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  rcases p748_3 (m.d 0 2) (by simp) with h751 | h751
                                  · rcases p748_3 (m.d 1 2) (by simp) with h752 | h752
                                    · linarith only [h0, h752, hlam]
                                    · linarith only [h684, h752, hlam]
                                  · linarith only [h751, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h2, h4, h685, h9, hlam, p696_1, p748_2]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h3, h4, h686, hlam, p696_1, p748_2]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h0, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h0, h691, h694, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p748_1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  rcases p748_3 (m.d 0 2) (by simp) with h761 | h761
                                  · rcases p748_3 (m.d 1 2) (by simp) with h762 | h762
                                    · rcases p748_3 (m.d 2 3) (by simp) with h763 | h763
                                      · linarith only [h684, h763, hlam]
                                      · linarith only [h690, h763, hlam]
                                    · linarith only [h762, hlam, p748_0]
                                  · linarith only [h5, h761, hlam]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  rcases p748_3 (m.d 0 2) (by simp) with h768 | h768
                                  · rcases p748_3 (m.d 1 2) (by simp) with h769 | h769
                                    · rcases p748_3 (m.d 2 3) (by simp) with h770 | h770
                                      · linarith only [h684, h770, hlam]
                                      · linarith only [h691, h770, hlam]
                                    · linarith only [h769, hlam, p748_0]
                                  · linarith only [h6, h768, hlam]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h4, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h684, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h0, h684, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p748_1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h0, h684, hc01, hc25, hlam, hphi, ht0b, ht5b, p748_1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h5, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h685, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h690, hlam, p748_1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h692, hlam, p748_1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h6, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h686, hlam, p748_0]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h691, hlam, p748_1]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [h690, hc34, hlam, hphi, ht45, p748_1, u5elo2]
                                · have p748_0 := h748c.1
                                  have p748_1 := h748c.2.1
                                  have p748_2 := h748c.2.2.1
                                  have p748_3 := h748c.2.2.2
                                  linarith only [hlam, p748_0]
                          · linarith only [h743, h8, hlam]
                        · linarith only [h6, h742, hlam]
                      · linarith only [h3, h741, hlam]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h2, hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h5, hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h7, hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h9, hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h3, hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h6, hlam, p696_1]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h8, hlam, p696_0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [h2, hc14, hlam, hphi, ht45, p696_1, u5elo0]
                    · have p696_0 := h696c.1
                      have p696_1 := h696c.2.1
                      have p696_2 := h696c.2.2.1
                      have p696_3 := h696c.2.2.2
                      linarith only [hlam, p696_0]
              · linarith only [h690, h691, h8, h9, hc34, hlam, hphi, ht45, u5elo4]
            · linarith only [h690, h7, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h687, h7, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h6, h684, h686, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
    · linarith only [h5, h684, h685, h9, hc23, hlam, hphi, ht34, ht45, u5elo4]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h808 | h808
    · rcases m.htr 1 2 5 (by decide) (by decide) with h809 | h809
      · rcases m.htr 1 3 4 (by decide) (by decide) with h810 | h810
        · rcases m.htr 1 4 5 (by decide) (by decide) with h811 | h811
          · linarith only [h2, h811, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h813 | h813
            · rcases m.htr 2 3 5 (by decide) (by decide) with h814 | h814
              · rcases m.htr 2 4 5 (by decide) (by decide) with h815 | h815
                · linarith only [h2, h684, h808, h815, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h817 | h817
                  · linarith only [h2, h808, h813, h817, h9, hlam]
                  · rcases h0bigk with h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h4, h684, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p819_1]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h1, h684, h809, h814, hc01, hc35, hlam, hphi, ht0b, ht5b, p819_1]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      rcases p819_3 (m.d 0 1) (by simp) with h823 | h823
                      · rcases p819_3 (m.d 0 2) (by simp) with h824 | h824
                        · linarith only [h0, h824, hlam]
                        · linarith only [h5, h824, hlam]
                      · linarith only [h2, h823, hlam]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      rcases p819_3 (m.d 0 1) (by simp) with h828 | h828
                      · rcases p819_3 (m.d 0 2) (by simp) with h829 | h829
                        · linarith only [h0, h829, hlam]
                        · linarith only [h6, h829, hlam]
                      · linarith only [h3, h828, hlam]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h0, hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h4, h684, h809, h813, h815, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p819_1]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      rcases p819_3 (m.d 0 1) (by simp) with h836 | h836
                      · rcases p819_3 (m.d 0 2) (by simp) with h837 | h837
                        · rcases p819_3 (m.d 0 3) (by simp) with h838 | h838
                          · linarith only [h4, h838, hlam]
                          · linarith only [h7, h838, hlam]
                        · linarith only [h5, h837, hlam]
                      · linarith only [h2, h836, hlam]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      rcases p819_3 (m.d 0 1) (by simp) with h843 | h843
                      · rcases p819_3 (m.d 0 2) (by simp) with h844 | h844
                        · rcases p819_3 (m.d 0 3) (by simp) with h845 | h845
                          · linarith only [h4, h845, hlam]
                          · linarith only [h8, h845, hlam]
                        · linarith only [h6, h844, hlam]
                      · linarith only [h3, h843, hlam]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h1, hlam, p819_1]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h4, hlam, p819_1]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      rcases p819_3 (m.d 0 1) (by simp) with h853 | h853
                      · rcases p819_3 (m.d 0 2) (by simp) with h854 | h854
                        · rcases p819_3 (m.d 0 3) (by simp) with h855 | h855
                          · rcases p819_3 (m.d 0 4) (by simp) with h856 | h856
                            · linarith only [h7, h856, hlam]
                            · rcases p819_3 (m.d 0 5) (by simp) with h858 | h858
                              · linarith only [h8, h858, hlam]
                              · linarith only [h858, h9, hlam]
                          · linarith only [h7, h855, hlam]
                        · linarith only [h5, h854, hlam]
                      · linarith only [h2, h853, hlam]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      rcases p819_3 (m.d 0 1) (by simp) with h864 | h864
                      · rcases p819_3 (m.d 0 2) (by simp) with h865 | h865
                        · rcases p819_3 (m.d 0 3) (by simp) with h866 | h866
                          · rcases p819_3 (m.d 0 4) (by simp) with h867 | h867
                            · linarith only [h7, h867, hlam]
                            · rcases p819_3 (m.d 0 5) (by simp) with h869 | h869
                              · linarith only [h8, h869, hlam]
                              · rcases h2bigk with h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  rcases p871_3 (m.d 0 2) (by simp) with h873 | h873
                                  · rcases p871_3 (m.d 1 2) (by simp) with h874 | h874
                                    · linarith only [h0, h874, hlam]
                                    · rcases p871_3 (m.d 2 3) (by simp) with h876 | h876
                                      · linarith only [h4, h876, hlam]
                                      · linarith only [h684, h876, hlam]
                                  · linarith only [h0, h873, hlam]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h0, h684, h809, h813, h815, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p871_1]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h4, h684, h809, h815, hlam, p871_2]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h4, h684, h809, hlam, p871_2]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h0, hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h684, hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h4, h684, h813, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p871_1]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h0, h4, h684, hc01, hc25, hlam, hphi, ht0b, ht5b, p871_1]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h4, hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h0, h4, h808, h813, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p871_1]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  rcases p871_3 (m.d 0 2) (by simp) with h891 | h891
                                  · rcases p871_3 (m.d 1 2) (by simp) with h892 | h892
                                    · linarith only [h684, h892, hlam]
                                    · linarith only [h808, h892, hlam]
                                  · linarith only [h5, h891, hlam]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  rcases p871_3 (m.d 0 2) (by simp) with h896 | h896
                                  · rcases p871_3 (m.d 1 2) (by simp) with h897 | h897
                                    · linarith only [h684, h897, hlam]
                                    · linarith only [h809, h897, hlam]
                                  · linarith only [h6, h896, hlam]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h5, hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h808, hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h813, hlam, p871_1]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h815, hlam, p871_1]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h6, hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h809, hlam, p871_0]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h814, hlam, p871_1]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [h813, hc34, hlam, hphi, ht45, p871_1, u5elo2]
                                · have p871_0 := h871c.1
                                  have p871_1 := h871c.2.1
                                  have p871_2 := h871c.2.2.1
                                  have p871_3 := h871c.2.2.2
                                  linarith only [hlam, p871_0]
                          · linarith only [h8, h866, hlam]
                        · linarith only [h6, h865, hlam]
                      · linarith only [h3, h864, hlam]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h2, hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h5, hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h7, hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h9, hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h3, hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h6, hlam, p819_1]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h8, hlam, p819_0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [h2, h808, h813, hc34, hlam, hphi, ht45, p819_1, u5elo0]
                    · have p819_0 := h819c.1
                      have p819_1 := h819c.2.1
                      have p819_2 := h819c.2.2.1
                      have p819_3 := h819c.2.2.2
                      linarith only [hlam, p819_0]
              · linarith only [h684, h814, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h4, h684, h7, h808, h813, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h7, h810, h9, hc13, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h808, h809, hc24, hlam, hphi, ht45, u5elo2]
    · linarith only [h5, h808, h9, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8

end R2N4
